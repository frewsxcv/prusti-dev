use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::Lowerer,
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        snapshots::IntoSnapshotLowerer,
    },
};

use vir_crate::{
    common::position::Positioned,
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

// Based on
// prusti-viper/src/encoder/middle/core_proof/predicates/owned/builders/owned_non_aliased/predicate_decl.rs,
// whch should be deleted.
pub(in super::super::super::super::super) struct SelfFramingAssertionToSnapshot {
    /// Mapping from place to snapshot. We use a vector because we need to know
    /// the insertion order.
    snap_calls: Vec<(vir_mid::Expression, vir_low::Expression)>,
    // Fields for encoding predicate body. In a language with inheritance, we
    // would have `place` and `root_address` in a subclass. However, in Rust we
    // need to play with `if` statements.
    place: Option<vir_low::VariableDecl>,
    root_address: Option<vir_low::VariableDecl>,
    heap: Option<vir_low::VariableDecl>,
}

impl SelfFramingAssertionToSnapshot {
    pub(in super::super::super::super::super) fn for_predicate_body(
        place: vir_low::VariableDecl,
        root_address: vir_low::VariableDecl,
    ) -> Self {
        Self {
            place: Some(place),
            root_address: Some(root_address),
            snap_calls: Vec::new(),
            heap: None,
        }
    }

    fn is_predicate_body(&self) -> bool {
        self.place.is_some()
    }

    fn predicate_place(&self) -> vir_low::Expression {
        self.place.clone().unwrap().into()
    }

    fn predicate_root_address(&self) -> vir_low::Expression {
        self.root_address.clone().unwrap().into()
    }

    // FIXME: Code duplication.
    fn pointer_deref_into_address<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if let Some(deref_place) = place.get_last_dereferenced_pointer() {
            let base_snapshot = self.expression_to_snapshot(lowerer, deref_place, true)?;
            let ty = deref_place.get_type();
            lowerer.pointer_address(ty, base_snapshot, place.position())
        } else {
            unreachable!()
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for SelfFramingAssertionToSnapshot {
    fn expression_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expression: &vir_mid::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        for (place, call) in &self.snap_calls {
            if place == expression {
                return Ok(call.clone());
            }
        }
        self.expression_to_snapshot_impl(lowerer, expression, expect_math_bool)
    }

    fn binary_op_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        op: &vir_mid::BinaryOp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut introduced_snap = false;
        if op.op_kind == vir_mid::BinaryOpKind::And {
            if let box vir_mid::Expression::AccPredicate(expression) = &op.left {
                if expression.predicate.is_owned_non_aliased() {
                    // The recursive call to `acc_predicate_to_snapshot` will
                    // add a snap call to `self.snap_calls`.
                    introduced_snap = true;
                }
            }
        }
        let expression = self.binary_op_to_snapshot_impl(lowerer, op, expect_math_bool)?;
        if introduced_snap {
            self.snap_calls.pop();
        }
        Ok(expression)
    }

    fn field_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        field: &vir_mid::Field,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &*field.base {
            vir_mid::Expression::Local(local) if self.is_predicate_body() => {
                assert!(local.variable.is_self_variable());
                let field_place = lowerer.encode_field_place(
                    &local.variable.ty,
                    &field.field,
                    self.predicate_place(),
                    field.position,
                )?;
                lowerer.owned_non_aliased_snap(
                    CallContext::BuiltinMethod,
                    &field.field.ty,
                    &field.field.ty,
                    field_place,
                    self.predicate_root_address(),
                    local.position,
                )
            }
            _ => self.field_to_snapshot_impl(lowerer, field, expect_math_bool),
        }
    }

    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        assert!(variable.is_self_variable(), "{} must be self", variable);
        Ok(vir_low::VariableDecl {
            name: variable.name.clone(),
            ty: self.type_to_snapshot(lowerer, &variable.ty)?,
        })
    }

    fn labelled_old_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _old: &vir_mid::LabelledOld,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn func_app_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _app: &vir_mid::FuncApp,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expect_math_bool);
        let expression = match &*acc_predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let ty = predicate.place.get_type();
                let place = lowerer.encode_expression_as_place(&predicate.place)?;
                let root_address = self.pointer_deref_into_address(lowerer, &predicate.place)?;
                let snapshot = true.into();
                let acc = lowerer.owned_non_aliased_predicate(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place.clone(),
                    root_address.clone(),
                    snapshot,
                    None,
                )?;
                let snap_call = lowerer.owned_non_aliased_snap(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    place,
                    root_address,
                    predicate.place.position(),
                )?;
                self.snap_calls.push((predicate.place.clone(), snap_call));
                acc
            }
            vir_mid::Predicate::MemoryBlockHeap(predicate) => {
                let place = lowerer.encode_expression_as_place(&predicate.address)?;
                let root_address = self.pointer_deref_into_address(lowerer, &predicate.address)?;
                use vir_low::macros::*;
                let compute_address = ty!(Address);
                let address = expr! {
                    ComputeAddress::compute_address([place], [root_address])
                };
                let size =
                    self.expression_to_snapshot(lowerer, &predicate.size, expect_math_bool)?;
                lowerer.encode_memory_block_stack_acc(address, size, acc_predicate.position)?
            }
            vir_mid::Predicate::MemoryBlockHeapDrop(predicate) => {
                let place = self.pointer_deref_into_address(lowerer, &predicate.address)?;
                let size =
                    self.expression_to_snapshot(lowerer, &predicate.size, expect_math_bool)?;
                lowerer.encode_memory_block_heap_drop_acc(place, size, acc_predicate.position)?
            }
            _ => unimplemented!("{acc_predicate}"),
        };
        Ok(expression)
    }

    fn call_context(&self) -> CallContext {
        todo!()
    }

    fn owned_non_aliased_snap(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _ty: &vir_mid::Type,
        _pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }
}
