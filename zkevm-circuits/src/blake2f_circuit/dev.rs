use crate::{
    blake2f_circuit::{Blake2fCircuit, Blake2fCircuitConfig, Blake2fCircuitConfigArgs},
    util::SubCircuitConfig,
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};

use eth_types::Field;
use std::hash::Hash;

impl<F: Field + Hash> Circuit<F> for Blake2fCircuit {
    type Config = Blake2fCircuitConfig<F>; // (Blake2fCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = Vec<u32>;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        let config =
            { Blake2fCircuitConfig::new(meta, Blake2fCircuitConfigArgs { rounds: params }) };
        // (config, challenges)
        config
    }

    fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!();
    }

    fn params(&self) -> Self::Params {
        self.inputs.iter().map(|input| input.rounds).collect()
    }

    fn synthesize(
        &self,
        config: Self::Config,
        // (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // let challenges = challenges.values(&mut layouter);

        config.table_compiled.synthesize(&mut layouter, None);
        let witness = config
            .wit_gen
            .clone()
            .map(|g| g.generate(self.inputs.clone()));
        config
            .compiled
            .synthesize(&mut layouter, witness.clone().as_ref());
        Ok(())
        // self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}
