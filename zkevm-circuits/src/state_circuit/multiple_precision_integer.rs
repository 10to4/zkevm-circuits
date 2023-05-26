use super::{lookups, param::*};
use crate::util::Expr;
use eth_types::{Address, Field, Word};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use std::marker::PhantomData;
use eth_types::ToLittleEndian;
use std::cmp::min;

pub trait ToLimbs<const N: usize> {
    fn to_limbs(&self) -> [u16; N];
}

impl ToLimbs<N_LIMBS_ACCOUNT_ADDRESS> for Address {
    fn to_limbs(&self) -> [u16; N_LIMBS_ACCOUNT_ADDRESS] {
        // address bytes are be.... maybe just have everything be later?
        // you will need this in the future later because it makes the key ordering more
        // obvious
        let le_bytes: Vec<_> = self.0.iter().rev().cloned().collect();
        le_bytes_to_limbs(&le_bytes).try_into().unwrap()
    }
}

impl ToLimbs<N_LIMBS_RW_COUNTER> for u32 {
    fn to_limbs(&self) -> [u16; N_LIMBS_RW_COUNTER] {
        le_bytes_to_limbs(&self.to_le_bytes()).try_into().unwrap()
    }
}

impl ToLimbs<N_LIMBS_WORD> for Word {
    fn to_limbs(&self) -> [u16; N_LIMBS_WORD] {
        le_bytes_to_limbs(&self.to_le_bytes()).try_into().unwrap()
    }
}

#[derive(Clone, Copy)]
pub struct Config<T, const N: usize>
where
    T: ToLimbs<N>,
{
    // TODO: we can save a column here by not storing the lsb, and then checking that
    // value - value_from_limbs(limbs.prepend(0)) fits into a limb.
    // Does this apply for RLC's too?
    pub limbs: [Column<Advice>; N],
    _marker: PhantomData<T>,
}

#[derive(Clone)]
pub struct Queries<F: Field, const N: usize> {
    pub limbs: [Expression<F>; N],
    pub limbs_prev: [Expression<F>; N],
}

impl<F: Field, const N: usize> Queries<F, N> {
    pub fn new<T: ToLimbs<N>>(meta: &mut VirtualCells<'_, F>, c: Config<T, N>) -> Self {
        Self {
            limbs: c.limbs.map(|limb| meta.query_advice(limb, Rotation::cur())),
            limbs_prev: c
                .limbs
                .map(|limb| meta.query_advice(limb, Rotation::prev())),
        }
    }
}

impl Config<Address, N_LIMBS_ACCOUNT_ADDRESS> {
    pub fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Address,
    ) -> Result<(), Error> {
        for (i, &limb) in value.to_limbs().iter().enumerate() {
            region.assign_advice(
                || format!("limb[{}] in address mpi", i),
                self.limbs[i],
                offset,
                || Value::known(F::from(limb as u64)),
            )?;
        }
        Ok(())
    }

    /// Annotates columns of this gadget embedded within a circuit region.
    pub fn annotate_columns_in_region<F: Field>(&self, region: &mut Region<F>, prefix: &str) {
        let mut annotations = Vec::new();
        for (i, _) in self.limbs.iter().enumerate() {
            annotations.push(format!("MPI_limbs_address_{}", i));
        }
        self.limbs
            .iter()
            .zip(annotations.iter())
            .for_each(|(col, ann)| region.name_column(|| format!("{}_{}", prefix, ann), *col));
    }
}

impl Config<u32, N_LIMBS_RW_COUNTER> {
    pub fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: u32,
    ) -> Result<(), Error> {
        for (i, &limb) in value.to_limbs().iter().enumerate() {
            region.assign_advice(
                || format!("limb[{}] in u32 mpi", i),
                self.limbs[i],
                offset,
                || Value::known(F::from(limb as u64)),
            )?;
        }
        Ok(())
    }

    /// Annotates columns of this gadget embedded within a circuit region.
    pub fn annotate_columns_in_region<F: Field>(&self, region: &mut Region<F>, prefix: &str) {
        let mut annotations = Vec::new();
        for (i, _) in self.limbs.iter().enumerate() {
            annotations.push(format!("MPI_limbs_u32_{}", i));
        }
        self.limbs
            .iter()
            .zip(annotations.iter())
            .for_each(|(col, ann)| region.name_column(|| format!("{}_{}", prefix, ann), *col));
    }
}

impl Config<Word, N_LIMBS_WORD> {
    pub fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Word,
    ) -> Result<(), Error> {
        for (i, &limb) in value.to_limbs().iter().enumerate() {
            region.assign_advice(
                || format!("limb[{}] in Word mpi", i),
                self.limbs[i],
                offset,
                || Value::known(F::from(limb as u64)),
            )?;
        }
        Ok(())
    }

    /// Annotates columns of this gadget embedded within a circuit region.
    pub fn annotate_columns_in_region<F: Field>(&self, region: &mut Region<F>, prefix: &str) {
        let mut annotations = Vec::new();
        for (i, _) in self.limbs.iter().enumerate() {
            annotations.push(format!("MPI_limbs_word_{}", i));
        }
        self.limbs
            .iter()
            .zip(annotations.iter())
            .for_each(|(col, ann)| region.name_column(|| format!("{}_{}", prefix, ann), *col));
    }
}

pub struct Chip<F: Field, T, const N_LIMBS: usize, const N_VALUES : usize>
where
    T: ToLimbs<N_LIMBS>,
{
    config: Config<T, N_LIMBS>,
    _marker: PhantomData<F>,
}

impl<F: Field, T, const N_LIMBS: usize, const N_VALUES: usize> Chip<F, T, N_LIMBS, N_VALUES>
where
    T: ToLimbs<N_LIMBS>,
{
    pub fn construct(config: Config<T, N_LIMBS>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        selector: Column<Fixed>,
        values: [Column<Advice>;N_VALUES],
        lookup: lookups::Config,
    ) -> Config<T, N_LIMBS> {

        let limbs_per_value = min(N_LIMBS, 8);
        
        let limbs = [0; N_LIMBS].map(|_| meta.advice_column());        

        for &limb in &limbs {
            lookup.range_check_u16(meta, "mpi limb fits into u16", |meta| {
                meta.query_advice(limb, Rotation::cur())
            });
        }
        
        for (n,value) in values.iter().enumerate() {
            meta.create_gate("mpi value matches claimed limbs", |meta| {
                let selector = meta.query_fixed(selector, Rotation::cur());
                let value_expr = meta.query_advice(*value, Rotation::cur());
                let value_limbs = &limbs[n*limbs_per_value..min((n+1)*limbs_per_value, N_LIMBS)];
                let limbs_expr = value_limbs.iter().map(|limb| meta.query_advice(*limb, Rotation::cur()));
                vec![selector * (value_expr - value_from_limbs(&limbs_expr.collect::<Vec<_>>()))]
            });    
        }

        Config {
            limbs,
            _marker: PhantomData,
        }
    }

    pub fn load(&self, _layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Ok(())
    }
}

fn le_bytes_to_limbs(bytes: &[u8]) -> Vec<u16> {
    bytes
        .iter()
        .tuples()
        .map(|(lo, hi)| u16::from_le_bytes([*lo, *hi]))
        .collect()
}

fn value_from_limbs<F: Field>(limbs: &[Expression<F>]) -> Expression<F> {
    limbs.iter().rev().fold(0u64.expr(), |result, limb| {
        limb.clone() + result * (1u64 << 16).expr()
    })
}
