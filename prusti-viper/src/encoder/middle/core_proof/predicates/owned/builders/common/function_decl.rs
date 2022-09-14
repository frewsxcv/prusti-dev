use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        snapshots::{
            IntoPureSnapshot, IntoSnapshot, SnapshotValidityInterface, SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};

use vir_crate::{
    common::{expression::ExpressionIterator, identifier::WithIdentifier},
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super) struct FunctionDeclBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super) lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    pub(in super::super) function_name: &'l str,
    pub(in super::super) ty: &'l vir_mid::Type,
    pub(in super::super) type_decl: &'l vir_mid::TypeDecl,
    pub(in super::super) parameters: Vec<vir_low::VariableDecl>,
    pub(in super::super) pres: Vec<vir_low::Expression>,
    pub(in super::super) posts: Vec<vir_low::Expression>,
    pub(in super::super) conjuncts: Option<Vec<vir_low::Expression>>,
    pub(in super::super) position: vir_low::Position,
}

impl<'l, 'p, 'v, 'tcx> FunctionDeclBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        function_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            function_name,
            ty,
            type_decl,
            parameters: Vec::new(),
            pres: Vec::new(),
            posts: Vec::new(),
            conjuncts: None,
            position,
            lowerer,
        })
    }

    pub(in super::super::super) fn build(self) -> SpannedEncodingResult<vir_low::FunctionDecl> {
        let return_type = self.ty.to_snapshot(self.lowerer)?;
        let function = vir_low::FunctionDecl {
            name: format!("{}${}", self.function_name, self.ty.get_identifier()),
            kind: vir_low::FunctionKind::Snap,
            parameters: self.parameters,
            body: self
                .conjuncts
                .map(|conjuncts| conjuncts.into_iter().conjoin()),
            pres: self.pres,
            posts: self.posts,
            return_type,
        };
        Ok(function)
    }

    pub(in super::super) fn create_lifetime_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.parameters
            .extend(self.lowerer.create_lifetime_parameters(self.type_decl)?);
        Ok(())
    }

    pub(in super::super) fn create_const_parameters(&mut self) -> SpannedEncodingResult<()> {
        for parameter in self.type_decl.get_const_parameters() {
            self.parameters
                .push(parameter.to_pure_snapshot(self.lowerer)?);
        }
        Ok(())
    }

    pub(in super::super) fn add_precondition(
        &mut self,
        assertion: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.pres.push(assertion);
        Ok(())
    }

    pub(in super::super) fn add_postcondition(
        &mut self,
        assertion: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.posts.push(assertion);
        Ok(())
    }

    pub(in super::super) fn array_length_int(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let array_length = array_length_mid.to_pure_snapshot(self.lowerer)?;
        let size_type_mid = self.lowerer.size_type_mid()?;
        self.lowerer
            .obtain_constant_value(&size_type_mid, array_length.into(), self.position)
    }

    pub(in super::super) fn result_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.ty.to_snapshot(self.lowerer)
    }

    pub(in super::super) fn result(&mut self) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new("__result", self.result_type()?))
    }

    pub(in super::super) fn add_validity_postcondition(&mut self) -> SpannedEncodingResult<()> {
        let result = self.result()?;
        let validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(result.into(), self.ty)?;
        self.add_postcondition(validity)
    }

    pub(in super::super) fn add_snapshot_len_equal_to_postcondition(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let snapshot = self.result()?;
        let snapshot_length = self
            .lowerer
            .obtain_array_len_snapshot(snapshot.into(), self.position)?;
        let array_length_int = self.array_length_int(array_length_mid)?;
        let expression = expr! {
            ([array_length_int] == [snapshot_length])
        };
        self.add_postcondition(expression)
    }
}
