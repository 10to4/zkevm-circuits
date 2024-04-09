use chiquito::backend::halo2::{chiquito2Halo2, ChiquitoHalo2};

use crate::util::{Challenges, SubCircuit, SubCircuitConfig};
use eth_types::Field;
use halo2_proofs::plonk::ConstraintSystem;

use super::{
    blake2f_chiquito::blake2f_circuit,
    blake2f_table::*,
    wit_gen::{Blake2fInputGen, InputValuesParse},
};

/// Blake2fCircuitConfig
#[derive(Clone, Debug)]
pub struct Blake2fCircuitConfig<F: Field> {
    circuit: ChiquitoHalo2<F, Vec<InputValuesParse<F>>, Blake2fInputGen<F>>,
    iv_table: ChiquitoHalo2<F, (), ()>,
    bits_table: ChiquitoHalo2<F, (), ()>,
    xor_4bits_table: ChiquitoHalo2<F, (), ()>,

    minimum_rows: usize,
}

/// Blake2fCircuitConfigArgs
pub struct Blake2fCircuitConfigArgs {}

impl<F: Field> SubCircuitConfig<F> for Blake2fCircuitConfig<F> {
    type ConfigArgs = Blake2fCircuitConfigArgs;

    fn new(meta: &mut ConstraintSystem<F>, _config: Self::ConfigArgs) -> Self {
        let lookup_iv_row = meta.fixed_column();
        let lookup_iv_value = meta.fixed_column();
        let lookup_iv_circuit = blake2f_iv_table_circuit(lookup_iv_row, lookup_iv_value);
        let mut iv_table = chiquito2Halo2(lookup_iv_circuit);
        iv_table.configure(meta);

        let lookup_4bits_row = meta.fixed_column();
        let lookup_4bits_value = meta.fixed_column();
        let lookup_4bits_circuit =
            blake2f_4bits_table_circuit(lookup_4bits_row, lookup_4bits_value);
        let mut bits_table = chiquito2Halo2(lookup_4bits_circuit);
        bits_table.configure(meta);

        let lookup_xor_4bits_row = meta.fixed_column();
        let lookup_xor_4bits_value = meta.fixed_column();
        let lookup_xor_4bits_circuit =
            blake2f_xor_4bits_table_circuit(lookup_xor_4bits_row, lookup_xor_4bits_value);
        let mut xor_4bits_table = chiquito2Halo2(lookup_xor_4bits_circuit);
        xor_4bits_table.configure(meta);

        let circuit_params = CircuitParams {
            lookup_iv_row,
            lookup_iv_value,
            lookup_4bits_row,
            lookup_4bits_value,
            lookup_xor_4bits_row,
            lookup_xor_4bits_value,
        };
        let mut circuit = chiquito2Halo2(blake2f_circuit(circuit_params));
        circuit.configure(meta);

        Self {
            circuit,
            iv_table,
            bits_table,
            xor_4bits_table,
            minimum_rows: meta.minimum_rows(),
        }
    }
}

/// Blake2fCircuit
#[derive(Default, Debug, Clone)]
pub struct Blake2fCircuit<F: Field> {
    /// input
    pub inputs: Vec<InputValuesParse<F>>,
}

impl<F: Field> Blake2fCircuit<F> {
    /// new Blake2fCircuit
    pub fn new(values: &[Vec<u8>]) -> Self {
        Blake2fCircuit {
            inputs: values
                .iter()
                .map(|input| InputValuesParse::new(input))
                .collect(),
        }
    }
}

impl<F: Field> SubCircuit<F> for Blake2fCircuit<F> {
    type Config = Blake2fCircuitConfig<F>;

    fn unusable_rows() -> usize {
        // No column queried at more than 3 distinct rotations, so returns 6 as
        // minimum unusable rows.
        6
    }

    fn instance(&self) -> Vec<Vec<F>> {
        Vec::new()
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &crate::witness::Block<F>) -> (usize, usize) {
        (
            block
                .blake2f_inputs
                .iter()
                .map(|inputs| inputs.len() + 1)
                .sum(),
            block.circuits_params.max_blake2f_rows,
        )
    }

    fn new_from_block(block: &crate::witness::Block<F>) -> Self {
        Self::new(&block.blake2f_inputs)
    }

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        _challenges: &Challenges<halo2_proofs::circuit::Value<F>>,
        layouter: &mut impl halo2_proofs::circuit::Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        config.bits_table.synthesize(layouter, ());
        config.iv_table.synthesize(layouter, ());
        config.xor_4bits_table.synthesize(layouter, ());
        config.circuit.synthesize(layouter, self.inputs.clone());
        Ok(())
    }
}
