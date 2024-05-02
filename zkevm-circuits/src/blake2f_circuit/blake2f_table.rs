use chiquito::{
    frontend::dsl::{cb::table, circuit, lb::LookupTable, CircuitContext, StepTypeSetupContext},
    plonkish::{
        compiler::{
            cell_manager::SingleRowCellManager, compile, config,
            step_selector::SimpleStepSelectorBuilder,
        },
        ir::{assignments::AssignmentGenerator, Circuit},
    },
    sbpir::query::Queriable,
};
use eth_types::Field;
use halo2_proofs::plonk::{Column, ConstraintSystem, Fixed};
use std::hash::Hash;

use super::{params::*, wit_gen::InputValuesParse};

#[derive(Clone, Debug)]
pub struct CircuitParams {
    pub tparams: TableParams,
    pub num: usize,
    pub rounds: Vec<u32>,
    pub max_rounds: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct TableParams {
    pub lookup_iv_row: Column<Fixed>,
    pub lookup_iv_value: Column<Fixed>,
    pub lookup_4bits_row: Column<Fixed>,
    pub lookup_4bits_value: Column<Fixed>,
    pub lookup_xor_4bits_row: Column<Fixed>,
    pub lookup_xor_4bits_value: Column<Fixed>,
}

impl TableParams {
    pub fn new<F: Field + Hash>(meta: &mut ConstraintSystem<F>) -> Self {
        let lookup_iv_row = meta.fixed_column();
        let lookup_iv_value = meta.fixed_column();
        let lookup_4bits_row = meta.fixed_column();
        let lookup_4bits_value = meta.fixed_column();
        let lookup_xor_4bits_row = meta.fixed_column();
        let lookup_xor_4bits_value = meta.fixed_column();

        Self {
            lookup_iv_row,
            lookup_iv_value,
            lookup_4bits_row,
            lookup_4bits_value,
            lookup_xor_4bits_row,
            lookup_xor_4bits_value,
        }
    }

    pub fn blake2f_table_circuit<F: Field + Hash>(
        &self,
    ) -> (Circuit<F>, std::option::Option<AssignmentGenerator<F, ()>>) {
        let blake2f_table_circuit = circuit::<F, (), _>("blake2f xor 4bits table", |ctx| {
            let lookup_iv_row: Queriable<F> = ctx.import_halo2_fixed("iv row", self.lookup_iv_row);
            let lookup_iv_value: Queriable<F> =
                ctx.import_halo2_fixed("iv value", self.lookup_iv_value);
            let lookup_4bits_row =
                ctx.import_halo2_fixed("lookup_4bits_row", self.lookup_4bits_row);
            let lookup_4bits_value =
                ctx.import_halo2_fixed("lookup_4bits_value", self.lookup_4bits_value);
            let lookup_xor_4bits_row =
                ctx.import_halo2_fixed("lookup_xor_4bits_row", self.lookup_xor_4bits_row);
            let lookup_xor_4bits_value =
                ctx.import_halo2_fixed("lookup_xor_4bits_value", self.lookup_xor_4bits_value);

            let iv_values = IV_VALUES;
            let xor_values = XOR_VALUES;
            ctx.pragma_num_steps((SPLIT_64BITS * SPLIT_64BITS) as usize);

            ctx.fixed_gen(move |ctx| {
                for (i, &value) in iv_values.iter().enumerate() {
                    ctx.assign(i, lookup_iv_row, F::from(i as u64));
                    ctx.assign(i, lookup_iv_value, F::from(value));
                }
                for i in 0..SPLIT_64BITS as usize {
                    ctx.assign(i, lookup_4bits_row, F::ONE);
                    ctx.assign(i, lookup_4bits_value, F::from(i as u64));
                }
                for (i, &value) in xor_values.iter().enumerate() {
                    ctx.assign(i, lookup_xor_4bits_row, F::from(i as u64));
                    ctx.assign(i, lookup_xor_4bits_value, F::from(value as u64));
                }
            });
        });

        let single_config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

        compile(single_config, &blake2f_table_circuit)
    }
}

#[derive(Clone, Copy)]
pub struct TableLists {
    pub iv_table: LookupTable,
    pub bits_table: LookupTable,
    pub xor_4bits_table: LookupTable,
}

impl TableLists {
    pub fn new<F: Field + Hash>(
        ctx: &mut CircuitContext<F, Vec<InputValuesParse>>,
        params: TableParams,
    ) -> TableLists {
        let lookup_iv_row: Queriable<F> = ctx.import_halo2_fixed("iv row", params.lookup_iv_row);
        let lookup_iv_value: Queriable<F> =
            ctx.import_halo2_fixed("iv value", params.lookup_iv_value);
        let lookup_4bits_row = ctx.import_halo2_fixed("lookup_4bits_row", params.lookup_4bits_row);
        let lookup_4bits_value =
            ctx.import_halo2_fixed("lookup_4bits_value", params.lookup_4bits_value);
        let lookup_xor_4bits_row =
            ctx.import_halo2_fixed("lookup_xor_4bits_row", params.lookup_xor_4bits_row);
        let lookup_xor_4bits_value =
            ctx.import_halo2_fixed("lookup_xor_4bits_value", params.lookup_xor_4bits_value);

        Self {
            iv_table: ctx.new_table(table().add(lookup_iv_row).add(lookup_iv_value)),
            bits_table: ctx.new_table(table().add(lookup_4bits_row).add(lookup_4bits_value)),
            xor_4bits_table: ctx.new_table(
                table()
                    .add(lookup_xor_4bits_row)
                    .add(lookup_xor_4bits_value),
            ),
        }
    }

    pub fn check_4bit<F: Field + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        bits: Queriable<F>,
    ) {
        ctx.add_lookup(self.bits_table.apply(1).apply(bits));
    }

    pub fn check_3bit<F: Field + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        bits: Queriable<F>,
    ) {
        ctx.add_lookup(self.bits_table.apply(1).apply(bits));
        ctx.add_lookup(self.bits_table.apply(1).apply(bits * 2));
    }

    pub fn check_xor<F: Field + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        b1: Queriable<F>,
        b2: Queriable<F>,
        xor: Queriable<F>,
    ) {
        ctx.add_lookup(self.xor_4bits_table.apply(b1 * BASE_4BITS + b2).apply(xor));
    }

    pub fn check_not<F: Field + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        b1: Queriable<F>,
        xor: Queriable<F>,
    ) {
        ctx.add_lookup(self.xor_4bits_table.apply(b1 * BASE_4BITS + 0xF).apply(xor));
    }

    pub fn check_iv<F: Field + Hash>(
        self,
        ctx: &mut StepTypeSetupContext<F>,
        i: usize,
        iv: Queriable<F>,
    ) {
        ctx.add_lookup(self.iv_table.apply(i).apply(iv));
    }
}
