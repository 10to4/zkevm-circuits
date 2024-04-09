use super::circuit::{Blake2fCircuit, Blake2fCircuitConfig, Blake2fCircuitConfigArgs};
use crate::util::{Challenges, SubCircuit, SubCircuitConfig};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};

use eth_types::Field;

// impl <F: Field> Circuit<F> for Blake2fCircuit<F> {
impl<F: Field> Circuit<F> for Blake2fCircuit<F> {
    type Config = (Blake2fCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let config = { Blake2fCircuitConfig::new(meta, Blake2fCircuitConfigArgs {}) };
        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);
        let _ = self.synthesize_sub(&config, &challenges, &mut layouter);

        Ok(())
    }
}
