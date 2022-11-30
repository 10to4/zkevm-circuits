use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols},
    mpt_circuit::helpers::{
        bytes_expr_into_rlc, compute_rlc, get_bool_constraint, get_is_extension_node,
        get_is_extension_node_even_nibbles, get_is_extension_node_long_odd_nibbles,
        get_is_extension_node_one_nibble,
    },
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{
        helpers::{get_branch_len, key_len_lookup, get_is_inserted_extension_node, range_lookups},
        param::{
            ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_ROWS_NUM, C_RLP_START, C_START, HASH_WIDTH,
            IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_C_EXT_LONGER_THAN_55_POS, IS_C_EXT_NODE_NON_HASHED_POS,
            IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
            IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
            IS_S_EXT_LONGER_THAN_55_POS, IS_S_EXT_NODE_NON_HASHED_POS, NIBBLES_COUNTER_POS,
            RLP_NUM, ACCOUNT_LEAF_ROWS_NUM, LEAF_ROWS_NUM, EXISTING_EXT_NODE_BEFORE_S,
            EXISTING_EXT_NODE_AFTER_S, EXTENSION_ROWS_NUM,
        },
    },
    mpt_circuit::{MPTConfig, ProofValues, FixedTableTag},
    table::KeccakTable,
};

use super::BranchCols;
use super::extension::{extension_node_rlp, extension_node_rlc, extension_node_selectors};

/*
An existing extension node (which gets modified because of an inserted extension node) occupies 6 rows.
The rows are the following:
EXISTING_EXT_NODE_BEFORE_SELECTORS
EXISTING_EXT_NODE_BEFORE_S
EXISTING_EXT_NODE_BEFORE_C
EXISTING_EXT_NODE_AFTER_SELECTORS
EXISTING_EXT_NODE_AFTER_S
EXISTING_EXT_NODE_AFTER_C

This file contains constraints for the existing extension node rows which appear after the leaf rows.
Some constraints are the same as as for the extension node rows that appear in the branch rows (RLP, RLC),
some are different (extension node selectors).

It needs to be checked that the newly inserted extension node branch only has two elements:
the leaf that caused a new extension node to be added and the old extension node that drifted into
a branch of the newly added extension node.
And it needs to be ensured that the drifted extension node is the same as it was before
the modification except for the change in its key (otherwise the attacker might hide one modification
- the modification of the drifted extension node).

The constraints that are implemented in `extension_node_key.rs` are not implemented for an existing
extension node as we do not have the underlying branch and other elements down to the leaf for it.
From `extension_node_key.rs` constraints we only need to implement the constraints related
to the second nibbles.

Note that `S` and `C` hashes (values in `c_main`) in the two `before` rows are the same. Likewise for
the two `after` rows. So the constraints like RLC and RLP are checked only for `S` rows (`c_main`
in `C` rows is never used, we need `C` rows only for the second nibbles).
*/

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeInsertedConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ExtensionNodeInsertedConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Clone,
        inter_root: Column<Advice>,
        position_cols: PositionCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        branch: BranchCols<F>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        keccak_table: KeccakTable,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        is_before: bool,
        check_zeros: bool,
    ) -> Self {
        let config = ExtensionNodeInsertedConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::from(1_u64));
        let c128 = Expression::Constant(F::from(128));
        let c160_inv = Expression::Constant(F::from(160_u64).invert().unwrap());
        let c192 = Expression::Constant(F::from(192));
        let rot_into_ext_node_selectors = -1;

        extension_node_rlp(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            rot_into_ext_node_selectors,
        );

        extension_node_rlc(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            accs.clone(),
            power_of_randomness.clone(),
            true,
        );
        
        extension_node_selectors(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            is_account_leaf_in_added_branch.clone(),
            rot_into_ext_node_selectors,
            true,
            true,
            is_before,
        );

        /*
        TODO: Correspondence between nibbles in C and bytes in S to be checked (for
        regular extension nodes this is done in extension_node_key.rs).
        */

        /*
        When we have an extension node in the first level of the account trie,
        its hash needs to be compared to the root of the trie.

        Note that existing extension node never appears in the first level (it can in `getProof`
        response) because the witness generator puts it after the leaf of the inserted extension
        node rows. So to check whether the existing extension node is in the first level, we need
        to check whether the inserted extension node is in the first level.
        */
        meta.lookup_any(
            "Account first level (existing) extension node hash - compared to root",
            |meta| {
                let q_enable = q_enable(meta);

                let mut rot_into_branch = - EXISTING_EXT_NODE_BEFORE_S - 1 - ACCOUNT_LEAF_ROWS_NUM;
                if !is_before {
                    rot_into_branch = - EXISTING_EXT_NODE_AFTER_S - 1 - ACCOUNT_LEAF_ROWS_NUM;
                }

                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation(rot_into_branch));

                let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                let root = meta.query_advice(inter_root, Rotation::cur());

                let selector = q_not_first * q_enable * (one.clone() - not_first_level);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * acc_c, keccak_input_rlc));

                let ext_len =
                    meta.query_advice(s_main.rlp1, Rotation::cur()) - c192.clone() + one.clone();

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * ext_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * root, keccak_output_rlc));

                table_map
            },
        );

        /*
        When extension node is in the first level of the storage trie, we need to check whether
        `hash(ext_node) = storage_trie_root`. We do this by checking whether
        `(ext_node_RLC, storage_trie_root_RLC)` is in the keccak table.

        Only check for the `before` row as this presents the extension node before the modification.
        The `after` row present the modified extension node which needs to be checked to correspond
        to the existing extension node that was modified due to inserted extension node.

        Note: extension node in the first level cannot be shorter than 32 bytes (it is always hashed).
        */
        if is_before {
            meta.lookup_any(
                "(Existing) extension node in first level of storage trie - hash compared to the storage root",
                |meta| {
                    let q_enable = q_enable(meta);

                    let rot_into_last_leaf_row = - EXISTING_EXT_NODE_BEFORE_S - 1;
                    let rot_into_branch_init = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;

                    // Check if there is an account above the existing extension node rows:
                    let is_account_leaf = meta.query_advice(
                        is_account_leaf_in_added_branch,
                        Rotation(rot_into_branch_init - 1),
                    ); 

                    let acc = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

                    let mut sc_hash = vec![];
                    // Note: storage root is always in `s_main.bytes`.
                    for column in s_main.bytes.iter() {
                        sc_hash.push(meta.query_advice(
                            *column,
                            Rotation(
                                rot_into_branch_init
                                    - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND),
                            ),
                        ));
                    }
                    let hash_rlc = bytes_expr_into_rlc(&sc_hash, power_of_randomness[0].clone());

                    let selector = q_enable * is_account_leaf;

                    let mut table_map = Vec::new();
                    let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                    table_map.push((selector.clone(), keccak_is_enabled));

                    let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                    table_map.push((selector.clone() * acc, keccak_input_rlc));

                    let ext_len =
                        meta.query_advice(s_main.rlp1, Rotation::cur()) - c192.clone() + one.clone();

                    let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                    table_map.push((selector.clone() * ext_len, keccak_input_len));

                    let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                    table_map.push((selector * hash_rlc, keccak_output_rlc));

                    table_map
                },
            );
        }
        // TODO: else

        /*
        Check whether the extension node hash is in the parent branch.
        That means we check whether
        `(extension_node_RLC, node_hash_RLC)` is in the keccak table where `node` is a parent
        brach child at `modified_node` position.
        */
        if is_before {
            meta.lookup_any("(Existing) extension node hash in parent branch", |meta| {
                let q_enable = q_enable(meta);
                let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let rot_into_last_leaf_row = - EXISTING_EXT_NODE_BEFORE_S - 1;
                let rot_into_branch_init = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;

                // Check if there is an account above the existing extension node rows:
                let is_account_leaf = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_ext_node_non_hashed =
                    meta.query_advice(s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM], Rotation(-1));

                let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

                let is_c_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init, true);

                let rot_into_branch = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM - EXTENSION_ROWS_NUM;

                let mod_node_hash_rlc_cur =
                    meta.query_advice(accs.s_mod_node_rlc, Rotation(rot_into_branch))
                    * is_c_inserted_ext_node.clone()
                    + meta.query_advice(accs.c_mod_node_rlc, Rotation(rot_into_branch))
                    * (one.clone() - is_c_inserted_ext_node);

                let selector = not_first_level
                    * q_enable
                    * (one.clone() - is_account_leaf)
                    * (one.clone() - is_ext_node_non_hashed);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * acc_c, keccak_input_rlc));

                let ext_len =
                    meta.query_advice(s_main.rlp1, Rotation::cur()) - c192.clone() + one.clone();

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * ext_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * mod_node_hash_rlc_cur, keccak_output_rlc));

                table_map
            });
        }

        meta.create_gate(
            "(Existing) extension node in parent branch (non-hashed extension node)",
            |meta| {
                let q_enable = q_enable(meta);
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());

                let rot_into_last_leaf_row = - EXISTING_EXT_NODE_BEFORE_S - 1;
                let rot_into_branch_init = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM + 1;

                // Check if there is an account above the existing extension node rows:
                let is_account_leaf = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_ext_node_non_hashed =
                    meta.query_advice(s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM], Rotation(-1));

                let mut constraints = vec![];

                let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

                let is_c_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init, true);

                let rot_into_branch = rot_into_last_leaf_row - LEAF_ROWS_NUM - BRANCH_ROWS_NUM - EXTENSION_ROWS_NUM;

                let mod_node_hash_rlc_cur =
                    meta.query_advice(accs.s_mod_node_rlc, Rotation(rot_into_branch))
                    * is_c_inserted_ext_node.clone()
                    + meta.query_advice(accs.c_mod_node_rlc, Rotation(rot_into_branch))
                    * (one.clone() - is_c_inserted_ext_node);


                /*
                When an extension node is not hashed, we do not check whether it is in a parent
                branch using a lookup (see above), instead we need to check whether the branch child
                at `modified_node` position is exactly the same as the extension node.
                */
                constraints.push((
                    "Non-hashed extension node in parent branch",
                    q_not_first
                        * q_enable
                        * (one.clone() - is_account_leaf)
                        * is_ext_node_non_hashed
                        * (mod_node_hash_rlc_cur - acc_c),
                ));

                constraints
            },
        );

        // TODO: constraints for `selectors` row

        /*
        Note: range_lookups for regular extension nodes are in `extension_node_key.rs`, but
        we do not have it for inserted extension nodes.
        */
        range_lookups(
            meta,
            q_enable.clone(),
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable.clone(),
            c_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            [s_main.rlp1, s_main.rlp2, c_main.rlp1, c_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        row: &MptWitnessRow<F>,
        offset: usize,
    ) { 
        if pv.is_extension_node {
            // [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,
            // 48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]

            // One nibble:
            // [226,16,160,172,105,12...
            // Could also be non-hashed branch:
            // [223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,
            // 128,128,128,128,128,128,128,128,128]

            // [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            // 213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,
            // 128,128] [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            // 0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,
            // 128,128,128,128,128,128,128,128,128,128,128]

            // Intermediate RLC value and mult (after key)
            // to know which mult we need to use in c_advices.
            pv.acc_s = F::zero();
            pv.acc_mult_s = F::one();
            let len: usize;
            if row.get_byte(1) <= 32 {
                // key length is 1
                len = 2 // [length byte, key]
            } else if row.get_byte(0) < 248 {
                len = (row.get_byte(1) - 128) as usize + 2;
            } else {
                len = (row.get_byte(2) - 128) as usize + 3;
            }
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut pv.acc_s,
                &mut pv.acc_mult_s,
                0,
                len,
            );

            // Final RLC value.
            pv.acc_c = pv.acc_s;
            pv.acc_mult_c = pv.acc_mult_s;
            let mut start = C_RLP_START + 1;
            let mut len = HASH_WIDTH + 1;
            if row.get_byte(C_RLP_START + 1) == 0 {
                // non-hashed branch in extension node
                start = C_START;
                len = HASH_WIDTH;
            }
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut pv.acc_c,
                &mut pv.acc_mult_c,
                start,
                len,
            );

            mpt_config
                .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, F::zero(), offset)
                .ok();

            region
                .assign_advice(
                    || "assign key_rlc".to_string(),
                    mpt_config.accumulators.key.rlc,
                    offset,
                    || Value::known(pv.extension_node_rlc),
                )
                .ok();
        }
    }
}
