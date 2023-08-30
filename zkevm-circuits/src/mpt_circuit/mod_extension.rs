use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::plonk::{Error, VirtualCells};

use super::{
    helpers::{ListKeyGadget, MPTConstraintBuilder, ListKeyWitness},
    rlp_gadgets::RLPItemWitness,
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{
        cached_region::CachedRegion, cell_manager::Cell, constraint_builder::RLCChainableRev,
        gadgets::LtGadget,
    },
    mpt_circuit::{
        helpers::{
            Indexable, ParentData, KECCAK, parent_memory, FIXED,
        },
        RlpItemType, witness_row::StorageRowType, FixedTableTag,
    },
};

#[derive(Clone, Debug, Default)]
pub(crate) struct ModExtensionGadget<F> {
    rlp_key: [ListKeyGadget<F>; 2],
    is_not_hashed: LtGadget<F, 2>,
    is_key_part_odd: [Cell<F>; 2],
    mult_key: Cell<F>,
}

impl<F: Field> ModExtensionGadget<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        parent_data: &mut [ParentData<F>; 2],
    ) -> Self {
        let mut config = ModExtensionGadget::default();

        circuit!([meta, cb], {
            let key_items = [
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::LongExtNodeKey as usize,
                    RlpItemType::Key,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ShortExtNodeKey as usize,
                    RlpItemType::Key,
                ),
            ];
            let rlp_value = [
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::LongExtNodeValue as usize,
                    RlpItemType::Node,
                )/*,
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ShortExtNodeKey as usize,
                    RlpItemType::Node,
                ),
                */
            ];

            for is_s in [true, false] {
                config.rlp_key[is_s.idx()] = ListKeyGadget::construct(cb, &key_items[is_s.idx()]);
                config.is_key_part_odd[is_s.idx()] = cb.query_cell();

                let first_byte = matchx! {
                    key_items[is_s.idx()].is_short() => key_items[is_s.idx()].bytes_be()[0].expr(),
                    key_items[is_s.idx()].is_long() => key_items[is_s.idx()].bytes_be()[1].expr(),
                    key_items[is_s.idx()].is_very_long() => key_items[is_s.idx()].bytes_be()[2].expr(),
                };
                require!((FixedTableTag::ExtOddKey.expr(),
                    first_byte, config.is_key_part_odd[is_s.idx()].expr()) => @FIXED);
            }
            

            let long_mod_ext_rlc = config
                .rlp_key[0]
                .rlc2(&cb.keccak_r)
                .rlc_chain_rev(rlp_value[0].rlc_chain_data());
        
            let long_mod_ext_num_bytes = config.rlp_key[0].rlp_list.num_bytes();

            let is_s = true;
            let parent_data = &mut parent_data[is_s.idx()];
            *parent_data =
                ParentData::load("leaf load", cb, &ctx.memory[parent_memory(is_s)], 0.expr());

            require!(vec![1.expr(), long_mod_ext_rlc.expr(), long_mod_ext_num_bytes.expr(), parent_data.hash.lo().expr(), parent_data.hash.hi().expr()] => @KECCAK);


            // TODO:
        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        rlp_values: &[RLPItemWitness],
        list_rlp_bytes: [Vec<u8>; 2],
    ) -> Result<(), Error> {
        let key_items = [
            rlp_values[StorageRowType::LongExtNodeKey as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeKey as usize].clone(),
        ];
        let value_bytes = [
            rlp_values[StorageRowType::LongExtNodeValue as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeValue as usize].clone(),
        ];

        let mut rlp_key = vec![ListKeyWitness::default(); 2];
        for is_s in [true, false] {
            rlp_key[is_s.idx()] = self.rlp_key[is_s.idx()].assign(
                region,
                offset,
                &list_rlp_bytes[is_s.idx()],
                &key_items[is_s.idx()],
            )?;
        }
        
        let mut first_key_byte = vec![0u8, 0u8];
        for is_s in [true, false] {
            first_key_byte[is_s.idx()] =
                key_items[is_s.idx()].bytes[rlp_key[is_s.idx()].key_item.num_rlp_bytes()];
        }
        // Compact encoding
        let is_key_part_odd = vec![first_key_byte[0] >> 4 == 1, first_key_byte[1] >> 4 == 1];
        for is_s in [true, false] {
            if is_key_part_odd[is_s.idx()] {
                assert!(first_key_byte[is_s.idx()] < 0b10_0000);
            } else {
                assert!(first_key_byte[is_s.idx()] == 0);
            }
        }

        for is_s in [true, false] {
            self.is_key_part_odd[is_s.idx()]
            .assign(region, offset, is_key_part_odd[is_s.idx()].scalar())?;
        }


        // TODO

        Ok(())
    }
}
