use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::{
            owned::builders::common::function_decl::FunctionDeclBuilder, OwnedNonAliasedUseBuilder,
            PredicatesMemoryBlockInterface, PredicatesOwnedInterface,
        },
        references::ReferencesInterface,
        snapshots::{
            IntoPureSnapshot, IntoSnapshotLowerer, SnapshotBytesInterface,
            SnapshotValidityInterface, SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface, footprint::FootprintInterface, pointers::PointersInterface,
    },
};

use vir_crate::{
    common::{expression::{QuantifierHelpers, ExpressionIterator}, position::Positioned},
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes}, operations::ty::Typed,
    },
};

pub(in super::super::super) struct OwnedNonAliasedSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
    inner: FunctionDeclBuilder<'l, 'p, 'v, 'tcx>,
    place: vir_low::VariableDecl,
    root_address: vir_low::VariableDecl,
    slice_len: Option<vir_mid::VariableDecl>,
}

impl<'l, 'p, 'v, 'tcx> OwnedNonAliasedSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<Self> {
        let slice_len = if ty.is_slice() {
            Some(vir_mid::VariableDecl::new(
                "slice_len",
                lowerer.size_type_mid()?,
            ))
        } else {
            None
        };
        Ok(Self {
            place: vir_low::VariableDecl::new("place", lowerer.place_type()?),
            root_address: vir_low::VariableDecl::new("root_address", lowerer.address_type()?),
            slice_len,
            inner: FunctionDeclBuilder::new(
                lowerer,
                "snap_owned_non_aliased",
                ty,
                type_decl,
                Default::default(),
            )?,
        })
    }

    pub(in super::super::super) fn build(self) -> SpannedEncodingResult<vir_low::FunctionDecl> {
        self.inner.build()
    }

    pub(in super::super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.place.clone());
        self.inner.parameters.push(self.root_address.clone());
        self.inner.create_lifetime_parameters()?;
        if let Some(slice_len_mid) = &self.slice_len {
            let slice_len = slice_len_mid.to_pure_snapshot(self.inner.lowerer)?;
            self.inner.parameters.push(slice_len);
        }
        self.inner.create_const_parameters()?;
        Ok(())
    }

    // FIXME: Code duplication.
    pub(in super::super::super) fn get_slice_len(
        &self,
    ) -> SpannedEncodingResult<vir_mid::VariableDecl> {
        Ok(self.slice_len.as_ref().unwrap().clone())
    }

    fn owned_predicate<G>(
        &mut self,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = OwnedNonAliasedUseBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            ty,
            generics,
            place,
            root_address,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    // FIXME: Code duplication with add_quantified_permission.
    pub(in super::super::super) fn add_quantifiers(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
        element_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let size_type_mid = self.inner.lowerer.size_type_mid()?;
        var_decls! {
            index_int: Int
        };
        let index = self.inner.lowerer.construct_constant_snapshot(
            &size_type_mid,
            index_int.clone().into(),
            self.inner.position,
        )?;
        let index_validity = self
            .inner
            .lowerer
            .encode_snapshot_valid_call_for_type(index.clone(), &size_type_mid)?;
        let array_length_int = self.inner.array_length_int(array_length_mid)?;
        let element_place = self.inner.lowerer.encode_index_place(
            self.inner.ty,
            self.place.clone().into(),
            index,
            self.inner.position,
        )?;
        let element_predicate_acc = {
            self.owned_predicate(
                element_type,
                element_type,
                element_place.clone(),
                self.root_address.clone().into(),
            )?
        };
        let result = self.inner.result()?.into();
        let element_snapshot = self.inner.lowerer.obtain_array_element_snapshot(
            result,
            index_int.clone().into(),
            self.inner.position,
        )?;
        let element_snap_call = self.inner.lowerer.owned_non_aliased_snap(
            CallContext::BuiltinMethod,
            element_type,
            element_type,
            element_place,
            self.root_address.clone().into(),
            self.inner.position,
        )?;
        let elements = vir_low::Expression::forall(
            vec![index_int.clone()],
            vec![vir_low::Trigger::new(vec![element_predicate_acc])],
            expr! {
                ([index_validity] && (index_int < [array_length_int])) ==>
                ([element_snapshot] == [element_snap_call])
            },
        );
        self.add_unfolding_postcondition(elements)
    }

    pub(in super::super::super) fn add_unfolding_postcondition(
        &mut self,
        body: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        let predicate = self.predcondition_predicate()?;
        let unfolding = predicate.into_unfolding(body);
        self.inner.add_postcondition(unfolding)
    }

    pub(in super::super::super) fn add_validity_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_validity_postcondition()
    }

    pub(in super::super::super) fn add_snapshot_len_equal_to_postcondition(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .add_snapshot_len_equal_to_postcondition(array_length_mid)
    }

    pub(in super::super::super) fn add_owned_precondition(&mut self) -> SpannedEncodingResult<()> {
        let predicate = self.predcondition_predicate()?;
        self.inner.add_precondition(predicate)
    }

    fn predcondition_predicate(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
        self.owned_predicate(
            self.inner.ty,
            self.inner.type_decl,
            self.place.clone().into(),
            self.root_address.clone().into(),
        )
    }

    fn compute_address(&self) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let compute_address = ty!(Address);
        let expression = expr! {
            ComputeAddress::compute_address(
                [self.place.clone().into()],
                [self.root_address.clone().into()]
            )
        };
        Ok(expression)
    }

    fn size_of(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner
            .lowerer
            .encode_type_size_expression2(self.inner.ty, self.inner.type_decl)
    }

    fn add_bytes_snapshot_equality_with(
        &mut self,
        snap_ty: &vir_mid::Type,
        snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let size_of = self.size_of()?;
        let bytes = self
            .inner
            .lowerer
            .encode_memory_block_bytes_expression(self.compute_address()?, size_of)?;
        let to_bytes = ty! { Bytes };
        let expression = expr! {
            [bytes] == (Snap<snap_ty>::to_bytes([snapshot]))
        };
        self.add_unfolding_postcondition(expression)
    }

    pub(in super::super::super) fn add_bytes_snapshot_equality(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let result = self.inner.result()?.into();
        self.add_bytes_snapshot_equality_with(self.inner.ty, result)
    }

    pub(in super::super::super) fn add_bytes_address_snapshot_equality(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let result = self.inner.result()?.into();
        let address_type = self.inner.lowerer.reference_address_type(self.inner.ty)?;
        self.inner
            .lowerer
            .encode_snapshot_to_bytes_function(&address_type)?;
        let target_address_snapshot = self.inner.lowerer.reference_address_snapshot(
            self.inner.ty,
            result,
            self.inner.position,
        )?;
        self.add_bytes_snapshot_equality_with(&address_type, target_address_snapshot)
    }

    pub(in super::super::super) fn create_field_snapshot_equality(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let result = self.inner.result()?;
        let field_place = self.inner.lowerer.encode_field_place(
            self.inner.ty,
            field,
            self.place.clone().into(),
            self.inner.position,
        )?;
        let field_snapshot = self.inner.lowerer.obtain_struct_field_snapshot(
            self.inner.ty,
            field,
            result.into(),
            self.inner.position,
        )?;
        let snap_call = self.inner.lowerer.owned_non_aliased_snap(
            CallContext::BuiltinMethod,
            &field.ty,
            &field.ty,
            field_place,
            self.root_address.clone().into(),
            self.inner.position,
        )?;
        Ok(expr! {
            [field_snapshot] == [snap_call]
        })
    }

    pub(in super::super::super) fn create_discriminant_snapshot_equality(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let result = self.inner.result()?;
        let discriminant_snapshot = self.inner.lowerer.obtain_enum_discriminant(
            result.into(),
            self.inner.ty,
            self.inner.position,
        )?;
        let discriminant_field = decl.discriminant_field();
        let discriminant_place = self.inner.lowerer.encode_field_place(
            self.inner.ty,
            &discriminant_field,
            self.place.clone().into(),
            self.inner.position,
        )?;
        let snap_call = self.inner.lowerer.owned_non_aliased_snap(
            CallContext::BuiltinMethod,
            &decl.discriminant_type,
            &decl.discriminant_type,
            discriminant_place,
            self.root_address.clone().into(),
            self.inner.position,
        )?;
        let snap_call_int = self.inner.lowerer.obtain_constant_value(
            &decl.discriminant_type,
            snap_call,
            self.inner.position,
        )?;
        Ok(expr! {
            [discriminant_snapshot] == [snap_call_int]
        })
    }

    pub(in super::super::super) fn create_variant_snapshot_equality(
        &mut self,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        use vir_low::macros::*;
        let result = self.inner.result()?;
        let discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
            result.clone().into(),
            self.inner.ty,
            self.inner.position,
        )?;
        let guard = expr! {
            [ discriminant_call ] == [ discriminant_value.into() ]
        };
        let variant_index = variant.name.clone().into();
        let variant_place = self.inner.lowerer.encode_enum_variant_place(
            self.inner.ty,
            &variant_index,
            self.place.clone().into(),
            self.inner.position,
        )?;
        let variant_snapshot = self.inner.lowerer.obtain_enum_variant_snapshot(
            self.inner.ty,
            &variant_index,
            result.into(),
            self.inner.position,
        )?;
        let variant_type = self.inner.ty.clone().variant(variant_index);
        let snap_call = self.inner.lowerer.owned_non_aliased_snap(
            CallContext::BuiltinMethod,
            &variant_type,
            &variant_type,
            variant_place,
            self.root_address.clone().into(),
            self.inner.position,
        )?;
        let equality = expr! {
            [variant_snapshot] == [snap_call]
        };
        Ok((guard, equality))
    }

    pub(in super::super::super) fn add_reference_snapshot_equalities(
        &mut self,
        decl: &vir_mid::type_decl::Reference,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let result = self.inner.result()?;
        let guard = self
            .inner
            .lowerer
            .encode_lifetime_const_into_pure_is_alive_variable(lifetime)?;
        let lifetime = lifetime.to_pure_snapshot(self.inner.lowerer)?;
        let deref_place = self
            .inner
            .lowerer
            .reference_deref_place(self.place.clone().into(), self.inner.position)?;
        let current_snapshot = self.inner.lowerer.reference_target_current_snapshot(
            self.inner.ty,
            result.clone().into(),
            self.inner.position,
        )?;
        let final_snapshot = self.inner.lowerer.reference_target_final_snapshot(
            self.inner.ty,
            result.clone().into(),
            self.inner.position,
        )?;
        let address = self.inner.lowerer.reference_address(
            self.inner.ty,
            result.clone().into(),
            self.inner.position,
        )?;
        let slice_len = self.inner.lowerer.reference_slice_len(
            self.inner.ty,
            result.into(),
            self.inner.position,
        )?;
        let equalities = if decl.uniqueness.is_unique() {
            let current_snap_call = self.inner.lowerer.unique_ref_snap(
                CallContext::BuiltinMethod,
                &decl.target_type,
                &decl.target_type,
                deref_place.clone(),
                address.clone(),
                lifetime.clone().into(),
                slice_len.clone(),
                false,
            )?;
            let final_snap_call = self.inner.lowerer.unique_ref_snap(
                CallContext::BuiltinMethod,
                &decl.target_type,
                &decl.target_type,
                deref_place,
                address,
                lifetime.into(),
                slice_len,
                true,
            )?;
            expr! {
                ([current_snapshot] == [current_snap_call]) &&
                ([final_snapshot] == [final_snap_call])
            }
        } else {
            unimplemented!();
            // expr! {
            //     [current_snapshot] == [current_snap_call]
            // }
        };
        let expression = expr! {
            guard ==> [equalities]
        };
        self.add_unfolding_postcondition(expression)
    }

    pub(in super::super::super) fn add_structural_invariant(
        &mut self,
        decl: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<()> {
        if let Some(invariant) = &decl.structural_invariant {
            use vir_low::macros::*;
            let result = self.inner.result()?;
            let mut equalities = Vec::new();
            for assertion in invariant {
                for (guard, place) in assertion.collect_guarded_owned_places() {
                    let parameter = self.inner.lowerer.compute_deref_parameter(&place)?;
                    let deref_result_snapshot = self.inner.lowerer.obtain_parameter_snapshot(
                        self.inner.ty,
                        &parameter.name,
                        parameter.ty,
                        result.clone().into(),
                        self.inner.position,
                    )?;
                    let ty = place.get_type();
                    let place_low = self.inner.lowerer.encode_expression_as_place(&place)?;
                    let root_address_low = {
                        // Code duplication with pointer_deref_into_address
                        let deref_place = place.get_last_dereferenced_pointer().unwrap();
                        // TODO: replace self in deref_place with result.
                        let base_snapshot = deref_place.to_pure_snapshot(self.inner.lowerer)?;
                        let ty = deref_place.get_type();
                        self.inner
                            .lowerer
                            .pointer_address(ty, base_snapshot, place.position())?
                    };
                    let snap_call = self.inner.lowerer.owned_non_aliased_snap(
                        CallContext::BuiltinMethod,
                        ty,
                        ty,
                        place_low,
                        root_address_low,
                        self.inner.position,
                    )?;
                    equalities.push(expr! {
                        [deref_result_snapshot] == [snap_call]
                    });
                }
            }
            self.add_unfolding_postcondition(equalities.into_iter().conjoin())?;
        }
        // // FIXME: Code duplication with encode_assign_method_rvalue
        // if let Some(invariant) = &decl.structural_invariant {
        //     let mut assertion_encoder =
        //         crate::encoder::middle::core_proof::builtin_methods::AssertionEncoder::new(
        //             &decl,
        //             Vec::new(),
        //             &None,
        //         );
        //     assertion_encoder.set_result_value(self.inner.result()?.clone());
        //     assertion_encoder.set_in_function();
        //     for assertion in invariant {
        //         let low_assertion = assertion_encoder.expression_to_snapshot(
        //             self.inner.lowerer,
        //             assertion,
        //             true,
        //         )?;
        //         self.add_unfolding_postcondition(low_assertion)?;
        //     }
        // }
        Ok(())
    }
}
