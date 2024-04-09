use chiquito::{
    ast::{query::Queriable, ToField},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Compiler,
    },
    dsl::{cb::lookup, circuit, StepTypeContext},
    ir::Circuit,
};
use eth_types::Field;
use halo2_proofs::plonk::{Column, Fixed};

use super::{params::*, wit_gen::Blake2fInputGen};

pub fn blake2f_iv_table_circuit<F: Field>(
    lookup_iv_row: Column<Fixed>,
    lookup_iv_value: Column<Fixed>,
) -> Circuit<F, (), ()> {
    let blake2f_iv_table_circuit = circuit::<F, (), (), _>("blake2f iv table", |ctx| {
        let lookup_iv_row = ctx.import_halo2_fixed("lookup_iv_row", lookup_iv_row);
        let lookup_iv_value = ctx.import_halo2_fixed("lookup_iv_value", lookup_iv_value);

        ctx.fixed_gen(move |ctx| {
            for (i, &value) in IV_VALUES.iter().enumerate() {
                ctx.assign(i, lookup_iv_row, i.field());
                ctx.assign(i, lookup_iv_value, value.field());
            }
        });
    });

    let compiler = Compiler::new(
        SingleRowCellManager::default(),
        SimpleStepSelectorBuilder {},
    );

    compiler.compile(&blake2f_iv_table_circuit)
}

// For range checking
pub fn blake2f_4bits_table_circuit<F: Field>(
    lookup_4bits_row: Column<Fixed>,
    lookup_4bits_value: Column<Fixed>,
) -> Circuit<F, (), ()> {
    let blake2f_4bits_table_circuit = circuit::<F, (), (), _>("blake2f 4bits table", |ctx| {
        let lookup_4bits_row = ctx.import_halo2_fixed("lookup_4bits_row", lookup_4bits_row);
        let lookup_4bits_value = ctx.import_halo2_fixed("lookup_4bits_value", lookup_4bits_value);

        ctx.fixed_gen(move |ctx| {
            for i in 0..SPLIT_64BITS as usize {
                ctx.assign(i, lookup_4bits_row, F::ONE);
                ctx.assign(i, lookup_4bits_value, i.field());
            }
        });
    });

    let compiler = Compiler::new(
        SingleRowCellManager::default(),
        SimpleStepSelectorBuilder {},
    );

    compiler.compile(&blake2f_4bits_table_circuit)
}

pub fn blake2f_xor_4bits_table_circuit<F: Field>(
    lookup_xor_4bits_row: Column<Fixed>,
    lookup_xor_4bits_value: Column<Fixed>,
) -> Circuit<F, (), ()> {
    let blake2f_xor_4bits_table_circuit =
        circuit::<F, (), (), _>("blake2f xor 4bits table", |ctx| {
            let lookup_xor_4bits_row =
                ctx.import_halo2_fixed("lookup_xor_4bits_row", lookup_xor_4bits_row);
            let lookup_xor_4bits_value =
                ctx.import_halo2_fixed("lookup_xor_4bits_value", lookup_xor_4bits_value);

            ctx.fixed_gen(move |ctx| {
                for (i, &value) in XOR_VALUES.iter().enumerate() {
                    ctx.assign(i, lookup_xor_4bits_row, i.field());
                    ctx.assign(i, lookup_xor_4bits_value, value.field());
                }
            });
        });

    let compiler = Compiler::new(
        SingleRowCellManager::default(),
        SimpleStepSelectorBuilder {},
    );

    compiler.compile(&blake2f_xor_4bits_table_circuit)
}

#[derive(Clone, Copy)]
pub struct CircuitParams {
    pub lookup_iv_row: Column<Fixed>,
    pub lookup_iv_value: Column<Fixed>,
    pub lookup_4bits_row: Column<Fixed>,
    pub lookup_4bits_value: Column<Fixed>,
    pub lookup_xor_4bits_row: Column<Fixed>,
    pub lookup_xor_4bits_value: Column<Fixed>,
}

pub fn check_4bit<F: Field>(
    ctx: &mut StepTypeContext<F, Blake2fInputGen<F>>,
    bits: Queriable<F>,
    table_row: Queriable<F>,
    table_value: Queriable<F>,
) {
    ctx.add_lookup(lookup().add(1, table_row).add(bits, table_value));
}

pub fn check_3bit<F: Field>(
    ctx: &mut StepTypeContext<F, Blake2fInputGen<F>>,
    bits: Queriable<F>,
    table_row: Queriable<F>,
    table_value: Queriable<F>,
) {
    ctx.add_lookup(lookup().add(1, table_row).add(bits, table_value));
    ctx.add_lookup(lookup().add(1, table_row).add(bits * 2, table_value));
}

pub fn check_xor<F: Field>(
    ctx: &mut StepTypeContext<F, Blake2fInputGen<F>>,
    b1: Queriable<F>,
    b2: Queriable<F>,
    xor: Queriable<F>,
    table_row: Queriable<F>,
    table_value: Queriable<F>,
) {
    ctx.add_lookup(
        lookup()
            .add(b1 * BASE_4BITS + b2, table_row)
            .add(xor, table_value),
    );
}

pub fn check_not<F: Field>(
    ctx: &mut StepTypeContext<F, Blake2fInputGen<F>>,
    b1: Queriable<F>,
    xor: Queriable<F>,
    table_row: Queriable<F>,
    table_value: Queriable<F>,
) {
    ctx.add_lookup(
        lookup()
            .add(b1 * BASE_4BITS + 0xF, table_row)
            .add(xor, table_value),
    );
}

pub fn check_iv<F: Field>(
    ctx: &mut StepTypeContext<F, Blake2fInputGen<F>>,
    i: usize,
    iv: Queriable<F>,
    table_row: Queriable<F>,
    table_value: Queriable<F>,
) {
    ctx.add_lookup(lookup().add(i, table_row).add(iv, table_value));
}
