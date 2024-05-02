//! The blake2f circuit implementation.

mod blake2f_chiquito;
mod blake2f_table;
mod params;

#[cfg(any(feature = "test", test, feature = "test-circuits"))]
// pub use circuit::Blake2fCircuit as TestBlake2fCircuit;

/// Blake2f circuit tester
#[cfg(any(feature = "test", test))]
pub mod dev;
/// Bytecode circuit tester
#[cfg(any(feature = "test", test))]
mod test;
mod wit_gen;

use crate::util::{Challenges, SubCircuit, SubCircuitConfig};
use chiquito::plonkish::{
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2},
    ir::assignments::AssignmentGenerator,
};
use eth_types::Field;
use halo2_proofs::plonk::{ConstraintSystem, Error};
use std::hash::Hash;

use crate::witness::Chunk;

use blake2f_chiquito::blake2f_circuit;
use blake2f_table::*;
use wit_gen::InputValuesParse;

/// Blake2fCircuitConfigArgs
pub struct Blake2fCircuitConfigArgs {
    // todo：
    // /// Challenges randomness
    // pub challenges: Challenges<Expression<F>>,
    /// Number of rounds for per input
    pub rounds: Vec<u32>,
}

/// Blake2fCircuitConfig
#[derive(Clone)]
pub struct Blake2fCircuitConfig<F: Field> {
    /// compiled
    pub compiled: ChiquitoHalo2<F>,
    /// table circuit
    pub table_compiled: ChiquitoHalo2<F>,
    wit_gen: Option<AssignmentGenerator<F, Vec<InputValuesParse>>>,
}

impl<F: Field + Hash> SubCircuitConfig<F> for Blake2fCircuitConfig<F> {
    type ConfigArgs = Blake2fCircuitConfigArgs;

    fn new(meta: &mut ConstraintSystem<F>, config: Self::ConfigArgs) -> Self {
        let params = TableParams::new(meta);
        let (table, _) = params.blake2f_table_circuit::<F>();
        let mut table_compiled = chiquito2Halo2(table);
        table_compiled.configure(meta);

        let max_rounds = config.rounds.iter().fold(12, |prev, &curr| prev.max(curr));
        let cparams = CircuitParams {
            num: config.rounds.len(),
            rounds: config.rounds.clone(),
            max_rounds,
            tparams: params,
        };
        let (circuit, wit_gen) = blake2f_circuit(cparams.clone());
        let mut compiled = chiquito2Halo2(circuit);
        compiled.configure(meta);

        Self {
            compiled,
            wit_gen,
            table_compiled,
        }
    }
}

/// Blake2fCircuit
#[derive(Default, Debug, Clone)]
pub struct Blake2fCircuit {
    /// inputs
    pub inputs: Vec<InputValuesParse>,
}

impl Blake2fCircuit {
    /// new Blake2fCircuit
    pub fn new(values: &[Vec<u8>]) -> Self {
        Self {
            inputs: values
                .iter()
                .map(|input| InputValuesParse::new(input))
                .collect(),
        }
    }

    /// new from inputs
    pub fn new_input(inputs: Vec<InputValuesParse>) -> Self {
        Self { inputs }
    }
}

impl<F: Field + Hash> SubCircuit<F> for Blake2fCircuit {
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
    fn min_num_rows_block(block: &crate::witness::Block<F>, _: &Chunk<F>) -> (usize, usize) {
        (
            block
                .blake2f_inputs
                .iter()
                .map(|inputs| inputs.len() + 1)
                .sum(),
            block.circuits_params.max_blake2f_rows,
        )
    }

    fn new_from_block(block: &crate::witness::Block<F>, _: &Chunk<F>) -> Self {
        Self::new(&block.blake2f_inputs)
    }

    fn synthesize_sub(
        &self,
        _config: &Self::Config,
        _challenges: &Challenges<halo2_proofs::circuit::Value<F>>,
        _layouter: &mut impl halo2_proofs::circuit::Layouter<F>,
    ) -> Result<(), Error> {
        Ok(())
    }
}
