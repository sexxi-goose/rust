//! See docs in build/expr/mod.rs

use crate::build::expr::category::Category;
use crate::build::ForGuard::{OutsideGuard, RefWithinGuard};
use crate::build::{BlockAnd, BlockAndExtension, Builder};
use crate::thir::*;
use rustc_hir::def_id::DefId;
use rustc_hir::HirId;
use rustc_middle::middle::region;
use rustc_middle::hir::place::ProjectionKind as HirProjectionKind;
use rustc_middle::mir::AssertKind::BoundsCheck;
use rustc_middle::mir::*;
use rustc_middle::ty::{self, CanonicalUserTypeAnnotation, Ty, TyCtxt, Variance};
use rustc_span::Span;
use rustc_target::abi::VariantIdx;

use rustc_index::vec::Idx;

#[derive(Copy, Clone)]
pub enum PlaceBase {
    Local(Local),
    Upvar { var_hir_id: HirId, closure_def_id: DefId, closure_kind: ty::ClosureKind },
}

/// `PlaceBuilder` is used to create places during MIR construction. It allows you to "build up" a
/// place by pushing more and more projections onto the end, and then convert the final set into a
/// place using the `into_place` method.
///
/// This is used internally when building a place for an expression like `a.b.c`. The fields `b`
/// and `c` can be progressively pushed onto the place builder that is created when converting `a`.
#[derive(Clone)]
struct PlaceBuilder<'tcx> {
    base: PlaceBase,
    projection: Vec<PlaceElem<'tcx>>,
}

/// Given a list of MIR projections, convert them to list of hir ProjectionKind.
fn convert_to_hir_projections_for_capture<'tcx>(
    mir_projections: &Vec<PlaceElem<'tcx>>) -> Vec<HirProjectionKind> {

    let mut hir_projections  = Vec::new();

    for mir_projection in mir_projections {
        let hir_projection = match mir_projection {
            ProjectionElem::Deref => HirProjectionKind::Deref,
            ProjectionElem::Field(field, _) => {
                // We will never encouter this for multivariant enums,
                // read the comment for `Downcast`.
                HirProjectionKind::Field(field.index() as u32, VariantIdx::new(0))
            },
            ProjectionElem::Downcast(..) => {
                // This projections exist only for enums that have
                // multiple variants. Since such enums that are captured
                // completely, we can stop here.
                break
            },
            ProjectionElem::Index(..)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. } => {
                // We don't capture array-access projections.
                // We can stop here as arrays are captured completely.
                break
            },
        };

        hir_projections.push(hir_projection);
    }

    hir_projections
}

fn is_ancestor_of_capture(
    proj_possible_ancestor: &Vec<HirProjectionKind>,
    proj_capture: &Vec<HirProjectionKind>) -> bool {

    for (proj_ans, proj_capture) in proj_possible_ancestor.iter().zip(proj_capture.iter()) {
        if proj_ans != proj_capture {
            return false;
        }
    }

    // In cases like
    // ```rust,ignore(wont-compile-because-pseudocode)
    // let c = ||  {
    //     x.0.1 += 1;
    //     let _ = x.0;
    // }
    // ```
    //
    // Here with `capture_disjoint_fields` enabled, x.0 won't be
    // captured but x.0.1 would be.
    //
    // Therefore we can't just return true here.
    proj_possible_ancestor.len() <= proj_capture.len()
}

/// Computes the index of a capture within the desugared closure provided the closure's
/// `closure_min_captures` and the capture's index of the capture in the
/// `ty::MinCaptureList` of the root variable `var_hir_id`.
fn compute_capture_idx<'tcx>(
    closure_min_captures: &ty::RootVariableMinCaptureList<'tcx>,
    var_hir_id: HirId,
    root_var_idx: usize) -> usize {
    let mut res = 0;
    for (var_id, capture_list) in closure_min_captures {
        if *var_id == var_hir_id {
            res += root_var_idx;
            break;
        } else {
            res += capture_list.len();
        }
    }

    res
}

/// Given a closure, returns the index of a capture within the desugared closure struct and the
/// `ty::CapturedPlace` which is the ancestor of the Place represented using the `var_hir_id`
/// and `projection`.
///
/// Note there will be atmost one ancestor for any given Place.
///
/// Returns None, when the ancestor is not found.
fn find_capture_matching_projections<'a, 'tcx>(
    typeck_results: &'a ty::TypeckResults<'tcx>,
    var_hir_id: HirId,
    closure_def_id: DefId,
    projections: &Vec<PlaceElem<'tcx>>,
) -> Option<(usize, &'a ty::CapturedPlace<'tcx>)> {
    let closure_min_captures = typeck_results
        .closure_min_captures
        .get(&closure_def_id);

    let closure_min_captures = if let Some(min_captures) = closure_min_captures {
        min_captures
    } else {
        return None;
    };

    let root_variable_min_captures =
        if let Some(captures) = closure_min_captures.get(&var_hir_id) {
        captures
    } else {
        return None
    };

    let hir_projections = convert_to_hir_projections_for_capture(projections);

    let find_ancestor = || {
        for (i, capture) in root_variable_min_captures.iter().enumerate() {
            let possible_ancestor_proj_kinds =
                capture.place.projections.iter().map(|proj| proj.kind).collect();
            if is_ancestor_of_capture(&possible_ancestor_proj_kinds, &hir_projections) {
                return Some((i, capture));
            }
        }
        return None;
    };


    if let Some((idx, capture)) = find_ancestor() {
        Some((compute_capture_idx(closure_min_captures, var_hir_id, idx), capture))
    } else {
        None
    }
}

/// Takes a PlaceBuilder and resolves the upvar (if any) within it, so that the
/// `PlaceBuilder` now starts from `PlaceBase::Local`.
///
/// Returns a Result with the error being the HirId of the Upvar that was not found.
fn to_upvars_resolved_place_builder<'a, 'tcx>(
    from_builder: PlaceBuilder<'tcx>,
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a ty::TypeckResults<'tcx>,
) -> Result<PlaceBuilder<'tcx>, HirId> {
    match from_builder.base {
        PlaceBase::Local(_) => Ok(from_builder),
        PlaceBase::Upvar { var_hir_id, closure_def_id, closure_kind } => {
            // Captures are represented using fields inside a structure.
            // This represents accessing self in the closure structure
            let local = PlaceBase::Local(Local::new(1));
            let mut place_builder = PlaceBuilder::from(local);
            match closure_kind {
                ty::ClosureKind::Fn | ty::ClosureKind::FnMut => {
                    place_builder = place_builder.deref();
                }
                ty::ClosureKind::FnOnce => {}
            }

            let (capture_index, capture) =
                if let Some(capture_details) = find_capture_matching_projections(
                    typeck_results,
                    var_hir_id,
                    closure_def_id,
                    &from_builder.projection,
                ) {
                    capture_details
                } else {
                    if !tcx.features().capture_disjoint_fields {
                        bug!(
                            "No associated capture found for {:?}[{:#?}] even though \
                            capture_disjoint_fields isn't enabled",
                            var_hir_id,
                            from_builder.projection,
                        )
                    } else {
                        // FIXME(project-rfc-2229#24): Handle this case properly
                        println!(
                            "No associated capture found for {:?}[{:#?}]",
                            var_hir_id,
                            from_builder.projection,
                        )
                    }
                    return Err(var_hir_id);
                };

            let closure_ty = typeck_results
                .node_type(tcx.hir().local_def_id_to_hir_id(closure_def_id.expect_local()));
            let substs = match closure_ty.kind() {
                ty::Closure(_, substs) => ty::UpvarSubsts::Closure(substs),
                ty::Generator(_, substs, _) => ty::UpvarSubsts::Generator(substs),
                _ => bug!("Lowering capture for non-closure type {:?}", closure_ty)
            };

            let var_ty = substs.tupled_upvars_ty().tuple_get_field(capture_index).unwrap();
            place_builder = place_builder.field(Field::new(capture_index), var_ty);

            place_builder = match capture.info.capture_kind {
                ty::UpvarCapture::ByRef(_) => place_builder.deref(),
                ty::UpvarCapture::ByValue(_) => place_builder,
            };

            let next_projection = capture.place.projections.len();
            let mut curr_projections = from_builder.projection;
            place_builder.projection.extend(curr_projections.drain(next_projection..));

            Ok(place_builder)
        }
    }
}

impl<'tcx> PlaceBuilder<'tcx> {
    fn into_place<'a>(
        self,
        tcx: TyCtxt<'tcx>,
        typeck_results: &'a ty::TypeckResults<'tcx>,
    ) -> Place<'tcx> {
        if let PlaceBase::Local(local) = self.base {
            Place { local, projection: tcx.intern_place_elems(&self.projection) }
        } else {
            self.expect_upvars_resolved(tcx, typeck_results).into_place(tcx, typeck_results)
        }
    }

    fn expect_upvars_resolved<'a>(
        self,
        tcx: TyCtxt<'tcx>,
        typeck_results: &'a ty::TypeckResults<'tcx>,
    ) -> PlaceBuilder<'tcx> {
        to_upvars_resolved_place_builder(self, tcx, typeck_results).unwrap()
    }

    fn field(self, f: Field, ty: Ty<'tcx>) -> Self {
        self.project(PlaceElem::Field(f, ty))
    }

    fn deref(self) -> Self {
        self.project(PlaceElem::Deref)
    }

    fn index(self, index: Local) -> Self {
        self.project(PlaceElem::Index(index))
    }

    fn project(mut self, elem: PlaceElem<'tcx>) -> Self {
        self.projection.push(elem);
        self
    }
}

impl<'tcx> From<PlaceBase> for PlaceBuilder<'tcx> {
    fn from(base: PlaceBase) -> Self {
        Self { base, projection: Vec::new() }
    }
}

impl<'a, 'tcx> Builder<'a, 'tcx> {
    /// Compile `expr`, yielding a place that we can move from etc.
    ///
    /// WARNING: Any user code might:
    /// * Invalidate any slice bounds checks performed.
    /// * Change the address that this `Place` refers to.
    /// * Modify the memory that this place refers to.
    /// * Invalidate the memory that this place refers to, this will be caught
    ///   by borrow checking.
    ///
    /// Extra care is needed if any user code is allowed to run between calling
    /// this method and using it, as is the case for `match` and index
    /// expressions.
    crate fn as_place<M>(&mut self, mut block: BasicBlock, expr: M) -> BlockAnd<Place<'tcx>>
    where
        M: Mirror<'tcx, Output = Expr<'tcx>>,
    {
        let place_builder = unpack!(block = self.as_place_builder(block, expr));
        block.and(place_builder.into_place(self.hir.tcx(), self.hir.typeck_results()))
    }

    /// This is used when constructing a compound `Place`, so that we can avoid creating
    /// intermediate `Place` values until we know the full set of projections.
    fn as_place_builder<M>(&mut self, block: BasicBlock, expr: M) -> BlockAnd<PlaceBuilder<'tcx>>
    where
        M: Mirror<'tcx, Output = Expr<'tcx>>,
    {
        let expr = self.hir.mirror(expr);
        self.expr_as_place(block, expr, Mutability::Mut, None)
    }

    /// Compile `expr`, yielding a place that we can move from etc.
    /// Mutability note: The caller of this method promises only to read from the resulting
    /// place. The place itself may or may not be mutable:
    /// * If this expr is a place expr like a.b, then we will return that place.
    /// * Otherwise, a temporary is created: in that event, it will be an immutable temporary.
    crate fn as_read_only_place<M>(
        &mut self,
        mut block: BasicBlock,
        expr: M,
    ) -> BlockAnd<Place<'tcx>>
    where
        M: Mirror<'tcx, Output = Expr<'tcx>>,
    {
        let place_builder = unpack!(block = self.as_read_only_place_builder(block, expr));
        block.and(place_builder.into_place(self.hir.tcx(), self.hir.typeck_results()))
    }

    /// This is used when constructing a compound `Place`, so that we can avoid creating
    /// intermediate `Place` values until we know the full set of projections.
    /// Mutability note: The caller of this method promises only to read from the resulting
    /// place. The place itself may or may not be mutable:
    /// * If this expr is a place expr like a.b, then we will return that place.
    /// * Otherwise, a temporary is created: in that event, it will be an immutable temporary.
    fn as_read_only_place_builder<M>(
        &mut self,
        block: BasicBlock,
        expr: M,
    ) -> BlockAnd<PlaceBuilder<'tcx>>
    where
        M: Mirror<'tcx, Output = Expr<'tcx>>,
    {
        let expr = self.hir.mirror(expr);
        self.expr_as_place(block, expr, Mutability::Not, None)
    }

    fn expr_as_place(
        &mut self,
        mut block: BasicBlock,
        expr: Expr<'tcx>,
        mutability: Mutability,
        fake_borrow_temps: Option<&mut Vec<Local>>,
    ) -> BlockAnd<PlaceBuilder<'tcx>> {
        debug!("expr_as_place(block={:?}, expr={:?}, mutability={:?})", block, expr, mutability);

        let this = self;
        let expr_span = expr.span;
        let source_info = this.source_info(expr_span);
        match expr.kind {
            ExprKind::Scope { region_scope, lint_level, value } => {
                this.in_scope((region_scope, source_info), lint_level, |this| {
                    let value = this.hir.mirror(value);
                    this.expr_as_place(block, value, mutability, fake_borrow_temps)
                })
            }
            ExprKind::Field { lhs, name } => {
                let lhs = this.hir.mirror(lhs);
                let place_builder =
                    unpack!(block = this.expr_as_place(block, lhs, mutability, fake_borrow_temps,));
                block.and(place_builder.field(name, expr.ty))
            }
            ExprKind::Deref { arg } => {
                let arg = this.hir.mirror(arg);
                let place_builder =
                    unpack!(block = this.expr_as_place(block, arg, mutability, fake_borrow_temps,));
                block.and(place_builder.deref())
            }
            ExprKind::Index { lhs, index } => this.lower_index_expression(
                block,
                lhs,
                index,
                mutability,
                fake_borrow_temps,
                expr.temp_lifetime,
                expr_span,
                source_info,
            ),
            ExprKind::UpvarRef { closure_def_id, var_hir_id } => {
                let upvar_id = ty::UpvarId::new(var_hir_id, closure_def_id.expect_local());
                this.lower_closure_capture(block, upvar_id)
            }

            ExprKind::VarRef { id } => {
                let place_builder = if this.is_bound_var_in_guard(id) {
                    let index = this.var_local_id(id, RefWithinGuard);
                    PlaceBuilder::from(PlaceBase::Local(index)).deref()
                } else {
                    let index = this.var_local_id(id, OutsideGuard);
                    PlaceBuilder::from(PlaceBase::Local(index))
                };
                block.and(place_builder)
            }

            ExprKind::PlaceTypeAscription { source, user_ty } => {
                let source = this.hir.mirror(source);
                let place_builder = unpack!(
                    block = this.expr_as_place(block, source, mutability, fake_borrow_temps,)
                );
                if let Some(user_ty) = user_ty {
                    let annotation_index =
                        this.canonical_user_type_annotations.push(CanonicalUserTypeAnnotation {
                            span: source_info.span,
                            user_ty,
                            inferred_ty: expr.ty,
                        });

                    let place =
                        place_builder.clone().into_place(this.hir.tcx(), this.hir.typeck_results());
                    this.cfg.push(
                        block,
                        Statement {
                            source_info,
                            kind: StatementKind::AscribeUserType(
                                box (
                                    place,
                                    UserTypeProjection { base: annotation_index, projs: vec![] },
                                ),
                                Variance::Invariant,
                            ),
                        },
                    );
                }
                block.and(place_builder)
            }
            ExprKind::ValueTypeAscription { source, user_ty } => {
                let source = this.hir.mirror(source);
                let temp =
                    unpack!(block = this.as_temp(block, source.temp_lifetime, source, mutability));
                if let Some(user_ty) = user_ty {
                    let annotation_index =
                        this.canonical_user_type_annotations.push(CanonicalUserTypeAnnotation {
                            span: source_info.span,
                            user_ty,
                            inferred_ty: expr.ty,
                        });
                    this.cfg.push(
                        block,
                        Statement {
                            source_info,
                            kind: StatementKind::AscribeUserType(
                                box (
                                    Place::from(temp),
                                    UserTypeProjection { base: annotation_index, projs: vec![] },
                                ),
                                Variance::Invariant,
                            ),
                        },
                    );
                }
                block.and(PlaceBuilder::from(PlaceBase::Local(temp)))
            }

            ExprKind::Array { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::Adt { .. }
            | ExprKind::Closure { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::LogicalOp { .. }
            | ExprKind::Box { .. }
            | ExprKind::Cast { .. }
            | ExprKind::Use { .. }
            | ExprKind::NeverToAny { .. }
            | ExprKind::Pointer { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::Borrow { .. }
            | ExprKind::AddressOf { .. }
            | ExprKind::Match { .. }
            | ExprKind::Loop { .. }
            | ExprKind::Block { .. }
            | ExprKind::Assign { .. }
            | ExprKind::AssignOp { .. }
            | ExprKind::Break { .. }
            | ExprKind::Continue { .. }
            | ExprKind::Return { .. }
            | ExprKind::Literal { .. }
            | ExprKind::ConstBlock { .. }
            | ExprKind::StaticRef { .. }
            | ExprKind::InlineAsm { .. }
            | ExprKind::LlvmInlineAsm { .. }
            | ExprKind::Yield { .. }
            | ExprKind::ThreadLocalRef(_)
            | ExprKind::Call { .. } => {
                // these are not places, so we need to make a temporary.
                debug_assert!(!matches!(Category::of(&expr.kind), Some(Category::Place)));
                let temp =
                    unpack!(block = this.as_temp(block, expr.temp_lifetime, expr, mutability));
                block.and(PlaceBuilder::from(PlaceBase::Local(temp)))
            }
        }
    }

    /// Lower a closure/generator capture by representing it as a field
    /// access within the desugared closure/generator.
    fn lower_closure_capture(
        &mut self,
        block: BasicBlock,
        upvar_id: ty::UpvarId,
    ) -> BlockAnd<PlaceBuilder<'tcx>> {
        let closure_ty = self
            .hir
            .typeck_results()
            .node_type(self.hir.tcx().hir().local_def_id_to_hir_id(upvar_id.closure_expr_id));

        let closure_kind = if let ty::Closure(_, closure_substs) = closure_ty.kind() {
            self.hir.infcx().closure_kind(closure_substs).unwrap()
        } else {
            // Generators are considered FnOnce.
            ty::ClosureKind::FnOnce
        };

        block.and(PlaceBuilder::from(PlaceBase::Upvar {
            var_hir_id: upvar_id.var_path.hir_id,
            closure_def_id: upvar_id.closure_expr_id.to_def_id(),
            closure_kind,
        }))
    }

    /// Lower an index expression
    ///
    /// This has two complications;
    ///
    /// * We need to do a bounds check.
    /// * We need to ensure that the bounds check can't be invalidated using an
    ///   expression like `x[1][{x = y; 2}]`. We use fake borrows here to ensure
    ///   that this is the case.
    fn lower_index_expression(
        &mut self,
        mut block: BasicBlock,
        base: ExprRef<'tcx>,
        index: ExprRef<'tcx>,
        mutability: Mutability,
        fake_borrow_temps: Option<&mut Vec<Local>>,
        temp_lifetime: Option<region::Scope>,
        expr_span: Span,
        source_info: SourceInfo,
    ) -> BlockAnd<PlaceBuilder<'tcx>> {
        let lhs = self.hir.mirror(base);

        let base_fake_borrow_temps = &mut Vec::new();
        let is_outermost_index = fake_borrow_temps.is_none();
        let fake_borrow_temps = fake_borrow_temps.unwrap_or(base_fake_borrow_temps);

        let mut base_place =
            unpack!(block = self.expr_as_place(block, lhs, mutability, Some(fake_borrow_temps),));

        // Making this a *fresh* temporary means we do not have to worry about
        // the index changing later: Nothing will ever change this temporary.
        // The "retagging" transformation (for Stacked Borrows) relies on this.
        let idx = unpack!(block = self.as_temp(block, temp_lifetime, index, Mutability::Not,));

        block = self.bounds_check(
            block,
            base_place.clone().into_place(self.hir.tcx(), self.hir.typeck_results()),
            idx,
            expr_span,
            source_info,
        );

        if is_outermost_index {
            self.read_fake_borrows(block, fake_borrow_temps, source_info)
        } else {
            base_place = base_place.expect_upvars_resolved(self.hir.tcx(), self.hir.typeck_results());
            self.add_fake_borrows_of_base(
                &base_place,
                block,
                fake_borrow_temps,
                expr_span,
                source_info,
            );
        }

        block.and(base_place.index(idx))
    }

    fn bounds_check(
        &mut self,
        block: BasicBlock,
        slice: Place<'tcx>,
        index: Local,
        expr_span: Span,
        source_info: SourceInfo,
    ) -> BasicBlock {
        let usize_ty = self.hir.usize_ty();
        let bool_ty = self.hir.bool_ty();
        // bounds check:
        let len = self.temp(usize_ty, expr_span);
        let lt = self.temp(bool_ty, expr_span);

        // len = len(slice)
        self.cfg.push_assign(block, source_info, len, Rvalue::Len(slice));
        // lt = idx < len
        self.cfg.push_assign(
            block,
            source_info,
            lt,
            Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(Place::from(index)), Operand::Copy(len)),
        );
        let msg = BoundsCheck { len: Operand::Move(len), index: Operand::Copy(Place::from(index)) };
        // assert!(lt, "...")
        self.assert(block, Operand::Move(lt), true, msg, expr_span)
    }

    fn add_fake_borrows_of_base(
        &mut self,
        base_place: &PlaceBuilder<'tcx>,
        block: BasicBlock,
        fake_borrow_temps: &mut Vec<Local>,
        expr_span: Span,
        source_info: SourceInfo,
    ) {
        let tcx = self.hir.tcx();
        let local = match base_place.base {
            PlaceBase::Local(local) => local,
            PlaceBase::Upvar { .. } => bug!("Expected PlacseBase::Local found Upvar")
        };

        let place_ty = Place::ty_from(local, &base_place.projection, &self.local_decls, tcx);
        if let ty::Slice(_) = place_ty.ty.kind() {
            // We need to create fake borrows to ensure that the bounds
            // check that we just did stays valid. Since we can't assign to
            // unsized values, we only need to ensure that none of the
            // pointers in the base place are modified.
            for (idx, elem) in base_place.projection.iter().enumerate().rev() {
                match elem {
                    ProjectionElem::Deref => {
                        let fake_borrow_deref_ty = Place::ty_from(
                            local,
                            &base_place.projection[..idx],
                            &self.local_decls,
                            tcx,
                        )
                        .ty;
                        let fake_borrow_ty =
                            tcx.mk_imm_ref(tcx.lifetimes.re_erased, fake_borrow_deref_ty);
                        let fake_borrow_temp =
                            self.local_decls.push(LocalDecl::new(fake_borrow_ty, expr_span));
                        let projection = tcx.intern_place_elems(&base_place.projection[..idx]);
                        self.cfg.push_assign(
                            block,
                            source_info,
                            fake_borrow_temp.into(),
                            Rvalue::Ref(
                                tcx.lifetimes.re_erased,
                                BorrowKind::Shallow,
                                Place { local, projection },
                            ),
                        );
                        fake_borrow_temps.push(fake_borrow_temp);
                    }
                    ProjectionElem::Index(_) => {
                        let index_ty = Place::ty_from(
                            local,
                            &base_place.projection[..idx],
                            &self.local_decls,
                            tcx,
                        );
                        match index_ty.ty.kind() {
                            // The previous index expression has already
                            // done any index expressions needed here.
                            ty::Slice(_) => break,
                            ty::Array(..) => (),
                            _ => bug!("unexpected index base"),
                        }
                    }
                    ProjectionElem::Field(..)
                    | ProjectionElem::Downcast(..)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. } => (),
                }
            }
        }
    }

    fn read_fake_borrows(
        &mut self,
        bb: BasicBlock,
        fake_borrow_temps: &mut Vec<Local>,
        source_info: SourceInfo,
    ) {
        // All indexes have been evaluated now, read all of the
        // fake borrows so that they are live across those index
        // expressions.
        for temp in fake_borrow_temps {
            self.cfg.push_fake_read(bb, source_info, FakeReadCause::ForIndex, Place::from(*temp));
        }
    }
}
