//! The blake2f circuit implementation.

mod blake2f_chiquito;
mod blake2f_table;
mod params;

/// Blake2f circuit
pub mod circuit;

/// Bytecode circuit tester
#[cfg(any(feature = "test", test))]
mod test;
#[cfg(any(feature = "test", test, feature = "test-circuits"))]
pub use circuit::Blake2fCircuit as TestBlake2fCircuit;

/// Blake2f circuit tester
#[cfg(any(feature = "test", test))]
pub mod dev;
mod wit_gen;
