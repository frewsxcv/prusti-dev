use super::{
    super::utils::place_domain_encoder::PlaceExpressionDomainEncoder, encoder::PlaceAddressEncoder,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer},
        pointers::PointersInterface,
        references::ReferencesInterface,
        snapshots::{IntoProcedureSnapshot, SnapshotVariablesInterface},
    },
};
use vir_crate::{
    common::position::Positioned,
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super) trait AddressesInterface {
    fn address_domain(&self) -> &'static str;
    fn address_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn address_null(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    /// Constructs a variable representing the address of the given MIR-level
    /// variable.
    fn root_address(
        &mut self,
        local: &vir_mid::expression::Local,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    /// Get the variable representing the root address of this place.
    fn extract_root_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_expression_as_place_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_field_address(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_enum_variant_address(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> AddressesInterface for Lowerer<'p, 'v, 'tcx> {
    fn address_domain(&self) -> &'static str {
        "Address"
    }
    fn address_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(self.address_domain())
    }
    fn address_null(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let address_type = self.address_type()?;
        self.create_domain_func_app(
            "Address",
            "null_address$",
            Vec::new(),
            address_type,
            position,
        )
    }
    fn root_address(
        &mut self,
        local: &vir_mid::expression::Local,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let address_variable =
            self.address_variable_version_at_label(&local.variable.name, old_label)?;
        Ok(vir_low::Expression::local(address_variable, local.position))
    }
    fn extract_root_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(place.is_place());
        let result = match place {
            vir_mid::Expression::Local(local) => self.root_address(local, &None)?,
            vir_mid::Expression::LabelledOld(_) => unimplemented!(),
            vir_mid::Expression::Deref(deref) => {
                // FIXME: Code duplication with PlaceAddressEncoder
                let base_snapshot = deref.base.to_procedure_snapshot(self)?;
                let ty = deref.base.get_type();
                if ty.is_reference() {
                    self.reference_address(ty, base_snapshot, place.position())?
                } else {
                    self.pointer_address(ty, base_snapshot, place.position())?
                }
            }
            _ => self.extract_root_address(place.get_parent_ref().unwrap())?,
        };
        Ok(result)
    }
    /// Emits code that represents the place's address.
    fn encode_expression_as_place_address(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut encoder = PlaceAddressEncoder::new();
        encoder.encode_expression(place, self)
    }
    fn encode_field_address(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_field_access_function_app("Address", base_address, base_type, field, position)
    }
    fn encode_enum_variant_address(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        self.encode_variant_access_function_app(
            "Address",
            base_address,
            base_type,
            variant,
            position,
        )
    }
}
