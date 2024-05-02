use chiquito::{
    frontend::dsl::{
        cb::{eq, select},
        circuit, StepTypeSetupContext, StepTypeWGHandler,
    },
    plonkish::{
        compiler::{
            cell_manager::SingleRowCellManager, compile, config,
            step_selector::SimpleStepSelectorBuilder,
        },
        ir::{assignments::AssignmentGenerator, Circuit},
    },
    poly::ToExpr,
    sbpir::query::Queriable,
};
use eth_types::Field;
use std::{fmt::Write, hash::Hash};

use super::{
    blake2f_table::{CircuitParams, TableLists},
    params::*,
    wit_gen::{FinalInput, GInput, InputValuesParse, PreInput},
};

struct GStepParams<F> {
    m_vec: Vec<Queriable<F>>,
    v_mid_va_bit_vec: Vec<Queriable<F>>,
    v_mid_vb_bit_vec: Vec<Queriable<F>>,
    v_mid_vc_bit_vec: Vec<Queriable<F>>,
    v_mid_vd_bit_vec: Vec<Queriable<F>>,
    v_xor_b_bit_vec: Vec<Queriable<F>>,
    v_xor_d_bit_vec: Vec<Queriable<F>>,
    input_vec: Vec<Queriable<F>>,
    output_vec: Vec<Queriable<F>>,
    b_bit: Queriable<F>,
    b_3bits: Queriable<F>,
}

pub fn u64_to_string(inputs: &[u64; 4]) -> [String; 4] {
    inputs
        .iter()
        .map(|input| {
            let mut s = String::new();
            for byte in input.to_le_bytes() {
                write!(&mut s, "{:02x}", byte).expect("Unable to write");
            }
            s
        })
        .collect::<Vec<String>>()
        .try_into()
        .unwrap()
}

fn split_4bit_signals<F: Field + Hash>(
    ctx: &mut StepTypeSetupContext<F>,
    tables: &TableLists,
    input: &[Queriable<F>],
    output: &[Vec<Queriable<F>>],
) {
    for (i, split_vec) in output.iter().enumerate() {
        let mut sum_value = 0.expr() * 1;

        for &bits in split_vec.iter().rev() {
            tables.check_4bit(ctx, bits);
            sum_value = sum_value * BASE_4BITS + bits;
        }
        ctx.constr(eq(sum_value, input[i]))
    }
}

// We check G function one time by calling twice g_setup function.c
// Because the G function can be divided into two similar parts.
fn g_setup<F: Field + Hash>(
    ctx: &mut StepTypeSetupContext<'_, F>,
    tables: TableLists,
    q_params: GStepParams<F>,
    (a, b, c, d): (usize, usize, usize, usize),
    (move1, move2): (u64, u64),
    s: usize,
    flag: bool,
) {
    let mut a_bits_sum_value = 0.expr() * 1;
    let mut a_bits_sum_mod_value = 0.expr() * 1;
    for (j, &bits) in q_params.v_mid_va_bit_vec.iter().rev().enumerate() {
        a_bits_sum_value = a_bits_sum_value * BASE_4BITS + bits;
        if j != 0 {
            a_bits_sum_mod_value = a_bits_sum_mod_value * BASE_4BITS + bits;
        }
        tables.check_4bit(ctx, bits);
    }
    // check v_mid_va_bit_vec = 4bit split of v[a] + v[b] + x
    ctx.constr(eq(
        a_bits_sum_value,
        q_params.input_vec[a] + q_params.input_vec[b] + q_params.m_vec[s],
    ));
    // check v[a] = (v[a] + v[b] + x) mod 2^64
    ctx.constr(eq(a_bits_sum_mod_value, q_params.output_vec[a]));

    // check d_bits_sum_value = 4bit split of v[b]
    let mut d_bits_sum_value = 0.expr() * 1;
    for &bits in q_params.v_mid_vd_bit_vec.iter().rev() {
        d_bits_sum_value = d_bits_sum_value * BASE_4BITS + bits;
        tables.check_4bit(ctx, bits);
    }
    ctx.constr(eq(d_bits_sum_value, q_params.input_vec[d]));

    let mut ad_xor_sum_value = 0.expr() * 1;
    for &bits in q_params.v_xor_d_bit_vec.iter().rev() {
        ad_xor_sum_value = ad_xor_sum_value * BASE_4BITS + bits;
    }
    // check v_xor_d_bit_vec =  4bit split of v[d]
    ctx.constr(eq(ad_xor_sum_value, q_params.output_vec[d]));
    // check v_xor_d_bit_vec[i] =  (v[d][i] ^ v[a][i]) >>> R1(or R3)
    for j in 0..SPLIT_64BITS as usize {
        tables.check_xor(
            ctx,
            q_params.v_mid_va_bit_vec[j],
            q_params.v_mid_vd_bit_vec[j],
            q_params.v_xor_d_bit_vec
                [(j + BASE_4BITS as usize - move1 as usize) % BASE_4BITS as usize],
        );
    }

    // check v[c] = (v[c] + v[d]) mod 2^64
    let mut c_bits_sum_value = 0.expr() * 1;
    let mut c_bits_sum_mod_value = 0.expr() * 1;
    for (j, &bits) in q_params.v_mid_vc_bit_vec.iter().rev().enumerate() {
        c_bits_sum_value = c_bits_sum_value * BASE_4BITS + bits;
        if j != 0 {
            c_bits_sum_mod_value = c_bits_sum_mod_value * BASE_4BITS + bits;
        }
        tables.check_4bit(ctx, bits);
    }
    // check v_mid_vc_bit_vec = 4bit split of (v[c] + v[d])
    ctx.constr(eq(
        c_bits_sum_value,
        q_params.input_vec[c] + q_params.output_vec[d],
    ));
    // check v[c] =  (v[c] + v[d] ) mod 2^64
    ctx.constr(eq(c_bits_sum_mod_value, q_params.output_vec[c]));

    let mut b_bits_sum_value = 0.expr() * 1;
    for &bits in q_params.v_mid_vb_bit_vec.iter().rev() {
        b_bits_sum_value = b_bits_sum_value * BASE_4BITS + bits;
        tables.check_4bit(ctx, bits);
    }

    // v_mid_vb_bit_vec = 4bit split of v[b]
    ctx.constr(eq(b_bits_sum_value, q_params.input_vec[b]));
    let mut bc_xor_sum_value = 0.expr() * 1;
    for (j, &bits) in q_params.v_xor_b_bit_vec.iter().rev().enumerate() {
        if j == 0 && flag {
            // b_bit * 8 + b_3bits = v_xor_b_bit_vec[0]
            bc_xor_sum_value = q_params.b_3bits * 1;
            ctx.constr(eq(q_params.b_bit * 8 + q_params.b_3bits, bits));
        } else {
            bc_xor_sum_value = bc_xor_sum_value * BASE_4BITS + bits;
        }
        tables.check_4bit(ctx, bits);
    }
    if flag {
        bc_xor_sum_value = bc_xor_sum_value * 2 + q_params.b_bit;

        ctx.constr(eq(q_params.b_bit * (q_params.b_bit - 1), 0));
        // To constraint b_3bits_vec[i/2] \in [0..8)
        tables.check_3bit(ctx, q_params.b_3bits);
    }
    // check v_xor_b_bit_vec = v[b]
    ctx.constr(eq(bc_xor_sum_value, q_params.output_vec[b]));

    // check v_xor_b_bit_vec[i] =  (v[b][i] ^ v[c][i]) >>> R2(or R4)
    for j in 0..SPLIT_64BITS as usize {
        tables.check_xor(
            ctx,
            q_params.v_mid_vb_bit_vec[j],
            q_params.v_mid_vc_bit_vec[j],
            q_params.v_xor_b_bit_vec
                [(j + BASE_4BITS as usize - move2 as usize) % BASE_4BITS as usize],
        );
    }
}

type Blake2fReturn<F> = (
    Circuit<F>,
    Option<AssignmentGenerator<F, Vec<InputValuesParse>>>,
);

pub fn blake2f_circuit<F: Field + Hash>(params: CircuitParams) -> Blake2fReturn<F> {
    let blake2f_circuit = circuit::<F, Vec<InputValuesParse>, _>("blake2f circuit", |ctx| {
        let params = params.clone();
        let tables = TableLists::new(ctx, params.tparams);

        let v_vec: Vec<Queriable<F>> = (0..V_LEN)
            .map(|i| ctx.forward(format!("v_vec[{}]", i).as_str()))
            .collect();
        let h_vec: Vec<Queriable<F>> = (0..H_LEN)
            .map(|i| ctx.forward(format!("h_vec[{}]", i).as_str()))
            .collect();
        let m_vec: Vec<Queriable<F>> = (0..M_LEN)
            .map(|i| ctx.forward(format!("m_vec[{}]", i).as_str()))
            .collect();
        let round = ctx.forward("round");
        let final_round = ctx.forward("final_round");

        let blake2f_pre_step = ctx.step_type_def("blake2f_pre_step", |ctx| {
            let v_vec = v_vec.clone();
            let wg_v_vec = v_vec.clone();

            let h_vec = h_vec.clone();
            let wg_h_vec = h_vec.clone();

            let m_vec = m_vec.clone();
            let wg_m_vec = m_vec.clone();

            let t0 = ctx.internal("t0");
            let t1 = ctx.internal("t1");
            let f = ctx.internal("f");

            // h_split_4bits_vec = 4bit split of h_vec
            let h_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..H_LEN)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| ctx.internal(format!("h_split_4bits_vec[{}][{}]", i, j).as_str()))
                        .collect()
                })
                .collect();
            let wg_h_split_4bits_vec = h_split_4bits_vec.clone();

            // m_split_4bits_vec = 4bit split of m_vec
            let m_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..M_LEN)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| ctx.internal(format!("m_split_4bits_vec[{}][{}]", i, j).as_str()))
                        .collect()
                })
                .collect();
            let wg_m_split_4bits_vec = m_split_4bits_vec.clone();

            // t_split_4bits_vec = 4bit split of t0 and t1
            let t_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..2)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| ctx.internal(format!("t_split_4bits_vec[{}][{}]", i, j).as_str()))
                        .collect()
                })
                .collect();
            let wg_t_split_4bits_vec = t_split_4bits_vec.clone();

            // iv_split_4bits_vec = 4bit split of IV[5], IV[6], IV[7]
            let iv_split_4bits_vec: Vec<Vec<Queriable<F>>> = (0..3)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| ctx.internal(format!("iv_split_4bits_vec[{}][{}]", i, j).as_str()))
                        .collect()
                })
                .collect();
            let wg_iv_split_4bits_vec = iv_split_4bits_vec.clone();

            // final_split_bits_vec = 4bit split of IV[5] xor t0, IV[6] xor t1, IV[7] xor
            // 0xFFFFFFFFFFFFFFFF,
            let final_split_bits_vec: Vec<Vec<Queriable<F>>> = (0..3)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| {
                            ctx.internal(format!("final_split_bits_vec[{}][{}]", i, j).as_str())
                        })
                        .collect()
                })
                .collect();
            let wg_final_split_bits_vec = final_split_bits_vec.clone();

            ctx.setup(move |ctx| {
                split_4bit_signals(ctx, &tables, &h_vec, &h_split_4bits_vec);

                // check inputs: m_vec
                split_4bit_signals(ctx, &tables, &m_vec, &m_split_4bits_vec);

                // check inputs: t0,t1
                split_4bit_signals(ctx, &tables, &[t0, t1], &t_split_4bits_vec);

                // check input f
                ctx.constr(eq(f * (f - 1), 0));

                // check v_vec
                for i in 0..H_LEN {
                    ctx.constr(eq(v_vec[i], h_vec[i]));
                }
                for (i, &iv) in v_vec[V_LEN / 2..V_LEN].iter().enumerate() {
                    tables.check_iv(ctx, i, iv);
                }

                // check the split-fields of v[12], v[13], v[14]
                split_4bit_signals(ctx, &tables, &v_vec[12..15], &iv_split_4bits_vec);

                // check v[12] := v[12] ^ (t mod 2**w)
                // check v[13] := v[13] ^ (t >> w)
                for (i, (final_plit_bits_value, (iv_split_bits_value, t_split_bits_value))) in
                    final_split_bits_vec
                        .iter()
                        .zip(iv_split_4bits_vec.iter().zip(t_split_4bits_vec.iter()))
                        .enumerate()
                        .take(2)
                {
                    let mut final_bits_sum_value = 0.expr() * 1;
                    for (&value, (&iv, &t)) in final_plit_bits_value.iter().rev().zip(
                        iv_split_bits_value
                            .iter()
                            .rev()
                            .zip(t_split_bits_value.iter().rev()),
                    ) {
                        tables.check_xor(ctx, iv, t, value);
                        final_bits_sum_value = final_bits_sum_value * BASE_4BITS + value;
                    }
                    ctx.constr(eq(final_bits_sum_value, v_vec[12 + i].next()))
                }

                // check if f, v[14] = v[14] ^ 0xffffffffffffffff else v[14]
                let mut final_bits_sum_value = 0.expr() * 1;
                for (&bits, &iv) in final_split_bits_vec[2]
                    .iter()
                    .rev()
                    .zip(iv_split_4bits_vec[2].iter().rev())
                {
                    tables.check_not(ctx, iv, bits);
                    final_bits_sum_value = final_bits_sum_value * BASE_4BITS + bits;
                }

                // check v_vec v_vec.next
                for &v in v_vec.iter().take(12) {
                    ctx.transition(eq(v, v.next()));
                }
                ctx.transition(eq(
                    select(f, final_bits_sum_value, v_vec[14]),
                    v_vec[14].next(),
                ));
                ctx.transition(eq(v_vec[15], v_vec[15].next()));
                // check h_vec h_vec.next
                for &h in h_vec.iter() {
                    ctx.transition(eq(h, h.next()));
                }
                // check m_vec m_vec.next
                for &m in m_vec.iter() {
                    ctx.transition(eq((round - final_round) * (m.next() - m), 0));
                }

                ctx.constr(eq(round, 0));
                ctx.transition(eq(round, round.next()));
                ctx.transition(eq(final_round, final_round.next()));
            });

            ctx.wg(move |ctx, inputs: PreInput<F>| {
                ctx.assign(round, inputs.round);
                ctx.assign(final_round, inputs.final_round);
                ctx.assign(t0, inputs.t0);
                ctx.assign(t1, inputs.t1);
                ctx.assign(f, inputs.f);
                for (&q, &v) in wg_v_vec.iter().zip(inputs.v_vec.iter()) {
                    ctx.assign(q, v)
                }
                for (&q, &v) in wg_h_vec.iter().zip(inputs.h_vec.iter()) {
                    ctx.assign(q, v)
                }
                for (&q, &v) in wg_m_vec.iter().zip(inputs.m_vec.iter()) {
                    ctx.assign(q, v)
                }
                for (q_vec, v_vec) in wg_h_split_4bits_vec
                    .iter()
                    .zip(inputs.h_split_4bits_vec.iter())
                {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
                for (q_vec, v_vec) in wg_m_split_4bits_vec
                    .iter()
                    .zip(inputs.m_split_4bits_vec.iter())
                {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
                for (q_vec, v_vec) in wg_t_split_4bits_vec
                    .iter()
                    .zip(inputs.t_split_4bits_vec.iter())
                {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
                for (q_vec, v_vec) in wg_iv_split_4bits_vec
                    .iter()
                    .zip(inputs.iv_split_4bits_vec.iter())
                {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
                for (q_vec, v_vec) in wg_final_split_bits_vec
                    .iter()
                    .zip(inputs.final_split_bits_vec.iter())
                {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
            })
        });

        let blake2f_g_setup_vec: Vec<StepTypeWGHandler<F, _, _>> = (0..params.max_rounds as usize)
            .map(|r| {
                ctx.step_type_def(format!("blake2f_g_setup_{}", r), |ctx| {
                    let v_vec = v_vec.clone();
                    let wg_v_vec = v_vec.clone();
                    let h_vec = h_vec.clone();
                    let wg_h_vec = h_vec.clone();
                    let m_vec = m_vec.clone();
                    let wg_m_vec = m_vec.clone();

                    // v_mid1_vec is the new v_vec after the first round call to the g_setup
                    // function
                    let v_mid1_vec: Vec<Queriable<F>> = (0..V_LEN)
                        .map(|i| ctx.internal(format!("v_mid1_vec[{}]", i).as_str()))
                        .collect();
                    let wg_v_mid1_vec = v_mid1_vec.clone();

                    // v_mid2_vec is the new v_vec after the second round call to the g_setup
                    // function
                    let v_mid2_vec: Vec<Queriable<F>> = (0..V_LEN)
                        .map(|i| ctx.internal(format!("v_mid2_vec[{}]", i).as_str()))
                        .collect();
                    let wg_v_mid2_vec = v_mid2_vec.clone();

                    // v_mid3_vec is the new v_vec after the third round to the g_setup function
                    let v_mid3_vec: Vec<Queriable<F>> = (0..V_LEN)
                        .map(|i| ctx.internal(format!("v_mid3_vec[{}]", i).as_str()))
                        .collect();
                    let wg_v_mid3_vec = v_mid3_vec.clone();

                    // v_mid4_vec is the new v_vec after the forth round to the g_setup function，as
                    // well as the final result of v_vec
                    let v_mid4_vec: Vec<Queriable<F>> = (0..V_LEN)
                        .map(|i| ctx.internal(format!("v_mid4_vec[{}]", i).as_str()))
                        .collect();
                    let wg_v_mid4_vec = v_mid4_vec.clone();

                    // v_mid_va_bit_vec = 4bit split of v[a] + v[b] + x(or y)
                    let v_mid_va_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                        .map(|i| {
                            (0..SPLIT_64BITS + 1)
                                .map(|j| {
                                    ctx.internal(format!("v_mid_va_bit_vec[{}][{}]", i, j).as_str())
                                })
                                .collect()
                        })
                        .collect();
                    let wg_v_mid_va_bit_vec = v_mid_va_bit_vec.clone();

                    // v_mid_vd_bit_vec = 4bit split of v[d]
                    let v_mid_vd_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                        .map(|i| {
                            (0..SPLIT_64BITS)
                                .map(|j| {
                                    ctx.internal(format!("v_mid_vd_bit_vec[{}][{}]", i, j).as_str())
                                })
                                .collect()
                        })
                        .collect();
                    let wg_v_mid_vd_bit_vec = v_mid_vd_bit_vec.clone();

                    // v_mid_vc_bit_vec = 4bit split of v[c] + v[d]
                    let v_mid_vc_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                        .map(|i| {
                            (0..SPLIT_64BITS + 1)
                                .map(|j| {
                                    ctx.internal(format!("v_mid_vc_bit_vec[{}][{}]", i, j).as_str())
                                })
                                .collect()
                        })
                        .collect();
                    let wg_v_mid_vc_bit_vec = v_mid_vc_bit_vec.clone();

                    // v_mid_vb_bit_vec = 4bit split of v[b]
                    let v_mid_vb_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                        .map(|i| {
                            (0..SPLIT_64BITS)
                                .map(|j| {
                                    ctx.internal(format!("v_mid_vb_bit_vec[{}][{}]", i, j).as_str())
                                })
                                .collect()
                        })
                        .collect();
                    let wg_v_mid_vb_bit_vec = v_mid_vb_bit_vec.clone();

                    // v_xor_d_bit_vec = 4bit split of  (v[d] ^ v[a]) >>> R1(or R3)
                    let v_xor_d_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                        .map(|i| {
                            (0..SPLIT_64BITS)
                                .map(|j| {
                                    ctx.internal(format!("v_xor_d_bit_vec[{}][{}]", i, j).as_str())
                                })
                                .collect()
                        })
                        .collect();
                    let wg_v_xor_d_bit_vec = v_xor_d_bit_vec.clone();

                    // v_xor_b_bit_vec = 4bit split of (v[b] ^ v[c]) >>> R2(or R4)
                    let v_xor_b_bit_vec: Vec<Vec<Queriable<F>>> = (0..G_ROUNDS)
                        .map(|i| {
                            (0..SPLIT_64BITS)
                                .map(|j| {
                                    ctx.internal(format!("v_xor_b_bit_vec[{}][{}]", i, j).as_str())
                                })
                                .collect()
                        })
                        .collect();
                    let wg_v_xor_b_bit_vec = v_xor_b_bit_vec.clone();

                    // b_bit_vec[i] * 8 + b_3bits_vec[i] = v_xor_b_bit_vec[i * 2 + 1][0]
                    // the step of v[b] := (v[b] ^ v[c]) >>> R4 needs to split a 4-bit value to a
                    // one-bit value and a 3-bit value
                    let b_bit_vec: Vec<Queriable<F>> = (0..G_ROUNDS / 2)
                        .map(|i| ctx.internal(format!("b_bit_vec[{}]", i).as_str()))
                        .collect();
                    let wg_b_bit_vec = b_bit_vec.clone();
                    let b_3bits_vec: Vec<Queriable<F>> = (0..G_ROUNDS / 2)
                        .map(|i| ctx.internal(format!("b_3bits_vec[{}]", i).as_str()))
                        .collect();
                    let wg_b_3bits_vec = b_3bits_vec.clone();

                    ctx.setup(move |ctx| {
                        let s = SIGMA_VALUES[r % 10];

                        for i in 0..G_ROUNDS as usize {
                            let mut input_vec = v_vec.clone();
                            let mut output_vec = v_mid1_vec.clone();
                            if i >= 8 {
                                if i % 2 == 0 {
                                    input_vec = v_mid2_vec.clone();
                                    output_vec = v_mid3_vec.clone();
                                } else {
                                    input_vec = v_mid3_vec.clone();
                                    output_vec = v_mid4_vec.clone();
                                }
                            } else if i % 2 == 1 {
                                input_vec = v_mid1_vec.clone();
                                output_vec = v_mid2_vec.clone();
                            }
                            let (mut a, mut b, mut c, mut d) =
                                (i / 2, 4 + i / 2, 8 + i / 2, 12 + i / 2);
                            if i / 2 == 4 {
                                (a, b, c, d) = (0, 5, 10, 15);
                            } else if i / 2 == 5 {
                                (a, b, c, d) = (1, 6, 11, 12);
                            } else if i / 2 == 6 {
                                (a, b, c, d) = (2, 7, 8, 13);
                            } else if i / 2 == 7 {
                                (a, b, c, d) = (3, 4, 9, 14);
                            }
                            let mut move1 = R1 / 4;
                            let mut move2 = R2 / 4;
                            if i % 2 == 1 {
                                move1 = R3 / 4;
                                move2 = (R4 + 1) / 4;
                            }
                            let q_params = GStepParams {
                                input_vec,
                                output_vec,
                                m_vec: m_vec.clone(),
                                v_mid_va_bit_vec: v_mid_va_bit_vec[i].clone(),
                                v_mid_vb_bit_vec: v_mid_vb_bit_vec[i].clone(),
                                v_mid_vc_bit_vec: v_mid_vc_bit_vec[i].clone(),
                                v_mid_vd_bit_vec: v_mid_vd_bit_vec[i].clone(),
                                v_xor_b_bit_vec: v_xor_b_bit_vec[i].clone(),
                                v_xor_d_bit_vec: v_xor_d_bit_vec[i].clone(),
                                b_bit: b_bit_vec[i / 2],
                                b_3bits: b_3bits_vec[i / 2],
                            };
                            g_setup(
                                ctx,
                                tables,
                                q_params,
                                (a, b, c, d),
                                (move1, move2),
                                s[i],
                                i % 2 == 1,
                            );
                        }

                        // check v_vec v_vec.next()
                        for (&v, &new_v) in v_vec.iter().zip(v_mid4_vec.iter()) {
                            ctx.transition(eq(new_v, v.next()));
                        }
                        // check h_vec h_vec.next()
                        for &h in h_vec.iter() {
                            ctx.transition(eq(h, h.next()));
                        }
                        // check m_vec m_vec.next()
                        for &m in m_vec.iter() {
                            ctx.transition(eq((round + 1 - final_round) * (m.next() - m), 0));
                        }
                        ctx.transition(eq(round + 1, round.next()));
                        ctx.transition(eq(final_round, final_round.next()));
                    });

                    ctx.wg(move |ctx, inputs: GInput<F>| {
                        ctx.assign(round, inputs.round);
                        ctx.assign(final_round, inputs.final_round);
                        for (&q, &v) in wg_v_vec.iter().zip(inputs.v_vec.iter()) {
                            ctx.assign(q, v)
                        }
                        for (&q, &v) in wg_h_vec.iter().zip(inputs.h_vec.iter()) {
                            ctx.assign(q, v)
                        }
                        for (&q, &v) in wg_m_vec.iter().zip(inputs.m_vec.iter()) {
                            ctx.assign(q, v)
                        }
                        for (&q, &v) in wg_v_mid1_vec.iter().zip(inputs.v_mid1_vec.iter()) {
                            ctx.assign(q, v)
                        }
                        for (&q, &v) in wg_v_mid2_vec.iter().zip(inputs.v_mid2_vec.iter()) {
                            ctx.assign(q, v)
                        }
                        for (&q, &v) in wg_v_mid3_vec.iter().zip(inputs.v_mid3_vec.iter()) {
                            ctx.assign(q, v)
                        }
                        for (&q, &v) in wg_v_mid4_vec.iter().zip(inputs.v_mid4_vec.iter()) {
                            ctx.assign(q, v)
                        }
                        for (q_vec, v_vec) in wg_v_mid_va_bit_vec
                            .iter()
                            .zip(inputs.v_mid_va_bit_vec.iter())
                        {
                            for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                                ctx.assign(q, v)
                            }
                        }
                        for (q_vec, v_vec) in wg_v_mid_vb_bit_vec
                            .iter()
                            .zip(inputs.v_mid_vb_bit_vec.iter())
                        {
                            for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                                ctx.assign(q, v)
                            }
                        }
                        for (q_vec, v_vec) in wg_v_mid_vc_bit_vec
                            .iter()
                            .zip(inputs.v_mid_vc_bit_vec.iter())
                        {
                            for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                                ctx.assign(q, v)
                            }
                        }
                        for (q_vec, v_vec) in wg_v_mid_vd_bit_vec
                            .iter()
                            .zip(inputs.v_mid_vd_bit_vec.iter())
                        {
                            for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                                ctx.assign(q, v)
                            }
                        }
                        for (q_vec, v_vec) in
                            wg_v_xor_d_bit_vec.iter().zip(inputs.v_xor_d_bit_vec.iter())
                        {
                            for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                                ctx.assign(q, v)
                            }
                        }
                        for (q_vec, v_vec) in
                            wg_v_xor_b_bit_vec.iter().zip(inputs.v_xor_b_bit_vec.iter())
                        {
                            for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                                ctx.assign(q, v)
                            }
                        }
                        for (&q, &v) in wg_b_bit_vec.iter().zip(inputs.b_bit_vec.iter()) {
                            ctx.assign(q, v)
                        }
                        for (&q, &v) in wg_b_3bits_vec.iter().zip(inputs.b_3bits_vec.iter()) {
                            ctx.assign(q, v)
                        }
                    })
                })
            })
            .collect();

        let blake2f_final_step = ctx.step_type_def("blake2f_final_step", |ctx| {
            let v_vec = v_vec.clone();
            let wg_v_vec = v_vec.clone();

            let h_vec = h_vec.clone();
            let wg_h_vec = h_vec.clone();

            let output_vec = m_vec.clone();
            let wg_output_vec = output_vec.clone();

            // v_split_bit_vec = 4bit split of v_vec
            let v_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..V_LEN)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| ctx.internal(format!("v_split_bit_vec[{}][{}]", i, j).as_str()))
                        .collect()
                })
                .collect();
            let wg_v_split_bit_vec = v_split_bit_vec.clone();

            // h_split_bit_vec = 4bit split of h_vec
            let h_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..H_LEN)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| ctx.internal(format!("h_split_bit_vec[{}][{}]", i, j).as_str()))
                        .collect()
                })
                .collect();
            let wg_h_split_bit_vec = h_split_bit_vec.clone();

            // v_xor_split_bit_vec = 4bit split of v[i] ^ v[i + 8]
            let v_xor_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..8)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| {
                            ctx.internal(format!("v_xor_split_bit_vec[{}][{}]", i, j).as_str())
                        })
                        .collect()
                })
                .collect();
            let wg_v_xor_split_bit_vec = v_xor_split_bit_vec.clone();

            // final_split_bit_vec = 4bit split of h[i] ^ v[i] ^ v[i + 8]
            let final_split_bit_vec: Vec<Vec<Queriable<F>>> = (0..8)
                .map(|i| {
                    (0..SPLIT_64BITS)
                        .map(|j| {
                            ctx.internal(format!("v_xor_split_bit_vec[{}][{}]", i, j).as_str())
                        })
                        .collect()
                })
                .collect();
            let wg_final_split_bit_vec = final_split_bit_vec.clone();

            ctx.setup(move |ctx| {
                // check split-fields of v_vec
                for (&v, v_split) in v_vec.iter().zip(v_split_bit_vec.iter()) {
                    let mut v_4bits_sum_value = 0.expr() * 1;
                    for &bits in v_split.iter().rev() {
                        v_4bits_sum_value = v_4bits_sum_value * BASE_4BITS + bits;
                        tables.check_4bit(ctx, bits);
                    }
                    ctx.constr(eq(v_4bits_sum_value, v));
                }

                // check split-fields of h_vec
                for (&h, h_split) in h_vec.iter().zip(h_split_bit_vec.iter()) {
                    let mut h_4bits_sum_value = 0.expr() * 1;
                    for &bits in h_split.iter().rev() {
                        h_4bits_sum_value = h_4bits_sum_value * BASE_4BITS + bits;
                        tables.check_4bit(ctx, bits);
                    }
                    ctx.constr(eq(h_4bits_sum_value, h));
                }

                // check split-fields of v[i] ^ v[i+8]
                for (xor_vec, (v1_vec, v2_vec)) in v_xor_split_bit_vec.iter().zip(
                    v_split_bit_vec[0..V_LEN / 2]
                        .iter()
                        .zip(v_split_bit_vec[V_LEN / 2..V_LEN].iter()),
                ) {
                    for (&xor, (&v1, &v2)) in xor_vec.iter().zip(v1_vec.iter().zip(v2_vec.iter())) {
                        tables.check_xor(ctx, v1, v2, xor);
                    }
                }

                // check split-fields of h[i] ^ v[i] ^ v[i+8]
                for (final_vec, (xor_vec, h_vec)) in final_split_bit_vec
                    .iter()
                    .zip(v_xor_split_bit_vec.iter().zip(h_split_bit_vec.iter()))
                {
                    for (&value, (&v1, &v2)) in
                        final_vec.iter().zip(xor_vec.iter().zip(h_vec.iter()))
                    {
                        tables.check_xor(ctx, v1, v2, value);
                    }
                }

                // check output = h[i] ^ v[i] ^ v[i+8]
                for (final_vec, &output) in final_split_bit_vec.iter().zip(output_vec.iter()) {
                    let mut final_4bits_sum_value = 0.expr() * 1;
                    for &value in final_vec.iter().rev() {
                        final_4bits_sum_value = final_4bits_sum_value * BASE_4BITS + value;
                    }
                    ctx.constr(eq(output, final_4bits_sum_value));
                }
                ctx.constr(eq(round, final_round));
            });

            ctx.wg(move |ctx, inputs: FinalInput<F>| {
                ctx.assign(round, inputs.round);
                ctx.assign(final_round, inputs.final_round);
                for (&q, &v) in wg_v_vec.iter().zip(inputs.v_vec.iter()) {
                    ctx.assign(q, v)
                }
                for (&q, &v) in wg_h_vec.iter().zip(inputs.h_vec.iter()) {
                    ctx.assign(q, v)
                }
                for (&q, &v) in wg_output_vec.iter().zip(inputs.output_vec.iter()) {
                    ctx.assign(q, v)
                }
                for (q_vec, v_vec) in wg_v_split_bit_vec.iter().zip(inputs.v_split_bit_vec.iter()) {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
                for (q_vec, v_vec) in wg_h_split_bit_vec.iter().zip(inputs.h_split_bit_vec.iter()) {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
                for (q_vec, v_vec) in wg_v_xor_split_bit_vec
                    .iter()
                    .zip(inputs.v_xor_split_bit_vec.iter())
                {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
                for (q_vec, v_vec) in wg_final_split_bit_vec
                    .iter()
                    .zip(inputs.final_split_bit_vec.iter())
                {
                    for (&q, &v) in q_vec.iter().zip(v_vec.iter()) {
                        ctx.assign(q, v)
                    }
                }
            })
        });

        let num_steps: usize = params.rounds.clone().iter().map(|&r| r as usize + 2).sum();
        ctx.pragma_num_steps(num_steps);
        ctx.pragma_first_step(&blake2f_pre_step);
        ctx.pragma_last_step(&blake2f_final_step); // todo

        ctx.trace(move |ctx, values| {
            assert_eq!(values.len(), params.num);

            for (i, values) in values.iter().enumerate() {
                let mut values = values.clone();

                let pre_inputs = values.pre_input_gen();
                ctx.add(&blake2f_pre_step, pre_inputs);

                assert_eq!(values.rounds, params.rounds[i]);

                for r in 0..values.rounds {
                    let ginputs = values.g_step_gen(r);
                    ctx.add(&blake2f_g_setup_vec[r as usize], ginputs);
                }

                let (final_inputs, output_vec_values) = values.final_input_gen();
                ctx.add(&blake2f_final_step, final_inputs);
                // ba80a53f981c4d0d, 6a2797b69f12f6e9, 4c212f14685ac4b7, 4b12bb6fdbffa2d1
                // 7d87c5392aab792d, c252d5de4533cc95, 18d38aa8dbf1925a,b92386edd4009923
                println!(
                    "output = {:?} \n         {:?}",
                    u64_to_string(&output_vec_values[0..4].try_into().unwrap()),
                    u64_to_string(&output_vec_values[4..8].try_into().unwrap())
                );
            }
        })
    });

    let single_config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
    let compiled = compile(single_config, &blake2f_circuit);
    compiled
}
