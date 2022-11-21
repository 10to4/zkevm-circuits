use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols},
    mpt_circuit::param::{
        HASH_WIDTH,
        IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS,
        IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, IS_EXT_LONG_ODD_C16_POS,
        IS_EXT_LONG_ODD_C1_POS, RLP_NUM, IS_S_EXT_LONGER_THAN_55_POS,
    },
    mpt_circuit::helpers::{
        bytes_expr_into_rlc, compute_rlc, get_bool_constraint, get_is_extension_node,
        get_is_extension_node_even_nibbles, get_is_extension_node_long_odd_nibbles,
        get_is_extension_node_one_nibble,
    },
};

pub(crate) fn extension_node_rlp<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
    position_cols: PositionCols<F>,
    s_main: MainCols<F>,
    c_main: MainCols<F>,
    rot_into_branch_init: i32,
) {
    let one = Expression::Constant(F::from(1_u64));
    let c33 = Expression::Constant(F::from(33));
    let c128 = Expression::Constant(F::from(128));
    let c160_inv = Expression::Constant(F::from(160_u64).invert().unwrap());
    let c192 = Expression::Constant(F::from(192));
    let c248 = Expression::Constant(F::from(248));

    meta.create_gate("Extension node RLP", |meta| {
        let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
        let q_enable = q_enable(meta);
        let mut constraints = vec![];

        // NOTE: even and odd is for number of nibbles that are compactly encoded.

        // To reduce the expression degree, we pack together multiple information.
        let is_ext_short_c16 = meta.query_advice(
            s_main.bytes[IS_EXT_SHORT_C16_POS - RLP_NUM],
            Rotation(rot_into_branch_init),
        );
        let is_ext_short_c1 = meta.query_advice(
            s_main.bytes[IS_EXT_SHORT_C1_POS - RLP_NUM],
            Rotation(rot_into_branch_init),
        );
        let is_ext_long_even_c16 = meta.query_advice(
            s_main.bytes[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM],
            Rotation(rot_into_branch_init),
        );
        let is_ext_long_even_c1 = meta.query_advice(
            s_main.bytes[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM],
            Rotation(rot_into_branch_init),
        );
        let is_ext_long_odd_c16 = meta.query_advice(
            s_main.bytes[IS_EXT_LONG_ODD_C16_POS - RLP_NUM],
            Rotation(rot_into_branch_init),
        );
        let is_ext_long_odd_c1 = meta.query_advice(
            s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM],
            Rotation(rot_into_branch_init),
        );
        let is_ext_longer_than_55 = meta.query_advice(
            s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
            Rotation(rot_into_branch_init),
        );

        // In C we have nibbles, we check below only for S.
        let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation::cur());
        let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());

        let is_short = is_ext_short_c16 + is_ext_short_c1;
        let is_even_nibbles = is_ext_long_even_c16 + is_ext_long_even_c1;
        let is_long_odd_nibbles = is_ext_long_odd_c16 + is_ext_long_odd_c1;

        /*
        This constraint prevents the attacker to set the number of nibbles to be even
        when it is not even.
        Note that when it is not even it holds `s_bytes0 != 0` (hexToCompact adds 16).

        If the number of nibbles is 1, like in
        `[226,16,160,172,105,12...`
        there is no byte specifying the length.
        If the number of nibbles is bigger than 1 and it is even, like in
        `[228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]`
        the second byte (`s_main.rlp2`) specifies the length (we need to subract 128 to get it),
        the third byte (`s_main.bytes[0]`) is 0.
        */
        constraints.push((
            "Long & even implies s_bytes0 = 0",
            q_not_first.clone()
                * q_enable.clone()
                * is_even_nibbles.clone()
                * s_bytes0.clone(),
        ));

        let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
        let is_branch_hashed = c_rlp2 * c160_inv.clone();

        /*
        We need to check that the length specified in `s_main.rlp1` corresponds to the actual
        length of the extension node.

        For example, in
        `[226,16,160,172,105,12...`
        we check that `226 - 192 = 1 + 32 + 1`.
        1 is for `s_main.rlp2`, 32 is for 32 bytes of the branch hash,
        1 is for the byte 160 which denotes the length
        of the hash (128 + 32).
        */
        constraints.push((
            "One nibble & hashed branch RLP",
            q_not_first.clone()
                * q_enable.clone()
                // when one nibble, extension node cannot be longer that 55
                * is_short.clone()
                * is_branch_hashed.clone()
                * (s_rlp1.clone() - c192.clone() - c33.clone() - one.clone()),
        ));

        let c_bytes0 = meta.query_advice(c_main.bytes[0], Rotation::cur());

        /*
        We need to check that the length specified in `s_main.rlp1` corresponds to the actual
        length of the extension node.
        
        For example, in
        `[223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128,128,128]`
        we check that `223 - 192 = 1 + 29 + 1`.
        1 is for `s_main.rlp2`,
        29 is for the branch RLP (which is not hashed because it is shorter than 32 bytes),
        1 is for `c_main.bytes[0]` which denotes the length of the branch RLP.
        */
        // TODO: prepare test
        constraints.push((
            "One nibble & non-hashed branch RLP",
            q_not_first.clone()
                * q_enable.clone()
                // when one nibble, extension node cannot be longer that 55
                * is_short
                * (one.clone() - is_branch_hashed.clone())
                * (s_rlp1.clone() - c192.clone() - one.clone() - (c_bytes0.clone() - c192.clone()) - one.clone()),
        ));

        let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());

        /*
        We need to check that the length specified in `s_main.rlp1` corresponds to the actual
        length of the extension node.
        
        For example, in
        `[228,130,0,149,160,114,253...`
        we check that `228 - 192 = (130 - 128) + 1 + 32 + 1`.
        1 is for `s_main.rlp2` which specifies the length of the nibbles part,
        32 is for the branch hash,
        1 is for the byte 160 which denotes the length
        of the hash (128 + 32).
        */
        constraints.push((
            "More than one nibble & hashed branch & ext not longer than 55 RLP",
            q_not_first.clone()
                * q_enable.clone()
                * (one.clone() - is_ext_longer_than_55.clone())
                * (is_even_nibbles.clone() + is_long_odd_nibbles.clone())
                * is_branch_hashed.clone()
                * (s_rlp1.clone() - c192.clone() - (s_rlp2.clone() - c128.clone()) - one.clone() - c33.clone()),
        ));

        /*
        We need to check that the length specified in `s_main.rlp1` corresponds to the actual
        length of the extension node.
        
        We check that `s_main.rlp1 - 192` = `s_main.rlp2 - 128 + 1 + c_main.bytes[0] - 192 + 1`.
        */
        constraints.push((
            "More than one nibble & non-hashed branch & ext not longer than 55 RLP",
            q_not_first.clone()
                * q_enable.clone()
                * (one.clone() - is_ext_longer_than_55.clone())
                * (is_even_nibbles + is_long_odd_nibbles)
                * (one.clone() - is_branch_hashed.clone())
                * (s_rlp1.clone() - c192.clone() - (s_rlp2.clone() - c128.clone()) - one.clone()
                    - (c_bytes0.clone() - c192.clone()) - one.clone()),
        ));

        /*
        Note: ext longer than 55 RLP cannot appear when there is only one nibble because in this case
        we would have 1 byte for a nibble and at most 32 bytes for branch.
        */

        /*
        When extension node RLP is longer than 55 bytes, the RLP has an additional byte
        at second position and the first byte specifies the length of the substream
        that specifies the length of the RLP. The substream is always just one byte: `s_main.rlp2`.
        And `s_main.rlp1 = 248` where `248 = 247 + 1` means the length of 1 byte.

        Example:
        `[248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,...`
        */
        constraints.push((
            "Extension longer than 55 RLP: s_rlp1 = 248",
            q_not_first.clone()
                * q_enable.clone()
                * is_ext_longer_than_55.clone()
                * (s_rlp1.clone() - c248.clone()),
        ));

        /*
        We need to check that the length specified in `s_main.rlp2` corresponds to the actual
        length of the extension node.

        Example:
        `[248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,...`
        
        We check that `s_main.rlp2 = (s_main.bytes[0] - 128) + 1 + 32 + 1`.
        `s_main.bytes[0] - 128` specifies the extension node nibbles part, 
        1 is for `s_main.rlp2` which specifies the length of the RLP stream,
        32 is for the branch hash,
        1 is for the byte 160 which denotes the length of the hash (128 + 32). 
        */
        // TODO: test
        constraints.push((
            "Hashed branch & ext longer than 55 RLP",
            q_not_first.clone()
                * q_enable.clone()
                * is_ext_longer_than_55.clone()
                * is_branch_hashed.clone()
                * (s_rlp2 - (s_bytes0.clone() - c128.clone()) - one.clone() - c33.clone()),
        ));

        /*
        We need to check that the length specified in `s_main.rlp2` corresponds to the actual
        length of the extension node.

        We check that `s_main.rlp2 = (s_main.bytes[0] - 128) + 1 + c_main.bytes[0] - 192 + 1`.
        `s_main.bytes[0] - 128` specifies the extension node nibbles part, 
        1 is for `s_main.rlp2` which specifies the length of the RLP stream,
        `c_main.bytes[0] - 192` is for the branch RLP (which is not hashed because it is shorter than 32 bytes),
        1 is for the byte 160 which denotes the length of the hash (128 + 32). 
        */
        // TODO: test
        constraints.push((
            "Non-hashed branch & ext longer than 55 RLP",
            q_not_first
                * q_enable
                * is_ext_longer_than_55
                * (one.clone() - is_branch_hashed)
                * (s_rlp1 - (s_bytes0 - c128.clone()) - one.clone()
                    - (c_bytes0 - c192.clone()) - one.clone()),
        ));

        /*
        Some observations:

        [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
        Note that the first element (228 in this case) can go much higher - for example, if there
        are 40 nibbles, this would take 20 bytes which would make the first element 248.

        If only one byte in key:
        [226,16,160,172,105,12...

        Extension node with non-hashed branch:
        List contains up to 55 bytes (192 + 55)
        [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

        List contains more than 55 bytes
        [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

        Note that the extension node can be much shorter than the one above - in case when
        there are less nibbles, so we cannot say that 226 appears as the first byte only
        when there are hashed nodes in the branch and there is only one nibble.
        Branch with two non-hashed nodes (that's the shortest possible branch):
        [217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
        Note: branch contains at least 26 bytes. 192 + 26 = 218

        If proofEl[0] <= 247 (length at most 55, so proofEl[1] doesn't specify the length of the whole
            remaining stream, only of the next substream)
        If proofEl[1] <= 128:
            There is only 1 byte for nibbles (keyLen = 1) and this is proofEl[1].
        Else:
            Nibbles are stored in more than 1 byte, proofEl[1] specifies the length of bytes.
        Else:
        proofEl[1] contains the length of the remaining stream.
        proofEl[2] specifies the length of the bytes (for storing nibbles).
        Note that we can't have only one nibble in this case.
        */

        constraints
    });
}

pub(crate) fn extension_node_rlc<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
    position_cols: PositionCols<F>,
    s_main: MainCols<F>,
    c_main: MainCols<F>,
    accs: AccumulatorCols<F>,
    power_of_randomness: [Expression<F>; HASH_WIDTH],
    is_s: bool,
) {
    meta.create_gate("Extension node RLC", |meta| {
        let mut constraints = vec![];
        let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
        let q_enable = q_enable(meta);

        let one = Expression::Constant(F::from(1_u64));
        let c160_inv = Expression::Constant(F::from(160_u64).invert().unwrap());

        let mut rot = 0;
        if !is_s {
            rot = -1;
        }

        /*
        s_rlp1, s_rlp2, s_bytes need to be the same in both extension rows.
        However, to make space for nibble witnesses, we put nibbles in
        extension row C s_bytes. So we use s_bytes from S row.
        */

        let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation(rot));
        let mut rlc = s_rlp1;
        let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation(rot));
        rlc = rlc + s_rlp2 * power_of_randomness[0].clone();

        let s_bytes_rlc = compute_rlc(
            meta,
            s_main.bytes.to_vec(),
            1,
            one.clone(),
            rot,
            power_of_randomness.clone(),
        );
        rlc = rlc + s_bytes_rlc;

        let acc_s = meta.query_advice(accs.acc_s.rlc, Rotation(rot));

        /*
        The intermediate RLC after `s_main` bytes needs to be properly computed.
        */
        constraints.push((
            "s_main RLC",
            q_not_first.clone()
                * q_enable.clone()
                * (rlc - acc_s.clone()),
        ));

        // We use rotation 0 in both cases from now on:
        let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
        let c160 = Expression::Constant(F::from(160_u64));

        // c_rlp2 = 160 when branch is hashed (longer than 31) and c_rlp2 = 0 otherwise
        let is_branch_hashed = c_rlp2.clone() * c160_inv.clone();

        /*
        When the branch is hashed, we have `c_rlp2 = 160` because it specifies the length of the
        hash: `32 = 160 - 128`.
        */
        constraints.push((
            "c_rlp2 = 160",
            q_not_first.clone()
                * q_enable.clone()
                * is_branch_hashed.clone()
                * (c_rlp2.clone() - c160),
        ));

        /*
        Note: hashed branch has 160 at c_rlp2 and hash in c_advices,
        non-hashed branch has 0 at c_rlp2 and all the bytes in c_advices
        */

        let acc_mult_s = meta.query_advice(accs.acc_s.mult, Rotation::cur());
        let c_advices0 = meta.query_advice(c_main.bytes[0], Rotation::cur());
        rlc = acc_s.clone() + c_rlp2 * acc_mult_s.clone();
        let c_advices_rlc = compute_rlc(
            meta,
            c_main.bytes.to_vec(),
            0,
            acc_mult_s.clone(),
            0,
            power_of_randomness.clone(),
        );
        rlc = rlc + c_advices_rlc;

        let mut rlc_non_hashed_branch = acc_s + c_advices0 * acc_mult_s.clone();
        let c_advices_rlc_non_hashed = compute_rlc(
            meta,
            c_main.bytes.iter().skip(1).copied().collect_vec(),
            0,
            acc_mult_s,
            0,
            power_of_randomness.clone(),
        );
        rlc_non_hashed_branch = rlc_non_hashed_branch + c_advices_rlc_non_hashed;

        let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

        /*
        Check whether the extension node RLC is properly computed.
        The RLC is used to check whether the extension node is a node at the appropriate position
        in the parent node. That means, it is used in a lookup to check whether
        `(extension_node_RLC, node_hash_RLC)` is in the keccak table.
        */
        constraints.push((
            "Hashed extension node RLC",
            q_not_first.clone()
                * q_enable.clone()
                * is_branch_hashed.clone()
                * (rlc - acc_c.clone()),
        ));

        /*
        Check whether the extension node (non-hashed) RLC is properly computed.
        The RLC is used to check whether the non-hashed extension node is a node at the appropriate position
        in the parent node. That means, there is a constraint to ensure that
        `extension_node_RLC = node_hash_RLC` for some `node` in parent branch.
        */
        constraints.push((
            "Non-hashed extension node RLC",
            q_not_first
                * q_enable
                * (one.clone() - is_branch_hashed)
                * (rlc_non_hashed_branch - acc_c),
        ));

        constraints
    });
}