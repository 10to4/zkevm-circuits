use super::params::*;
use eth_types::Field;
use std::hash::Hash;

#[derive(Default, Debug, Clone)]
pub struct InputValuesParse {
    pub rounds: u32,
    pub h_vec_values: Vec<u64>,
    pub m_vec_values: Vec<u64>,
    pub v_vec_values: Vec<u64>,
    pub iv_vec_values: Vec<u64>,
    pub t_vec_values: Vec<u64>,
    pub f: bool,
}

impl InputValuesParse {
    pub fn new(inputs: &Vec<u8>) -> Self {
        assert_eq!(inputs.len(), INPUT_LEN);
        let rounds: u32 = u32::from_be_bytes(inputs[0..4].try_into().unwrap());
        let h_vec_values: Vec<u64> = (0..H_LEN)
            .map(|i| u64::from_le_bytes(inputs[4 + i * 8..4 + (i + 1) * 8].try_into().unwrap()))
            .collect();

        let m_vec_values: Vec<u64> = (0..M_LEN)
            .map(|i| {
                u64::from_le_bytes(
                    inputs[4 + (H_LEN + i) * 8..4 + (H_LEN + i + 1) * 8]
                        .try_into()
                        .unwrap(),
                )
            })
            .collect();
        let iv_vec_values = IV_VALUES.to_vec();

        let mut v_vec_values = h_vec_values.clone();
        v_vec_values.append(&mut iv_vec_values.clone());

        let t_vec_values: Vec<u64> = (0..2)
            .map(|i| {
                u64::from_le_bytes(
                    inputs[4 + (H_LEN + M_LEN + i) * 8..4 + (H_LEN + M_LEN + i + 1) * 8]
                        .try_into()
                        .unwrap(),
                )
            })
            .collect();

        let f = inputs[4 + (H_LEN + M_LEN + 2) * 8];
        assert_eq!(f * (f - 1), 0);

        Self {
            h_vec_values,
            m_vec_values,
            v_vec_values,
            iv_vec_values,
            t_vec_values,
            f: f != 0,
            rounds,
        }
    }

    pub fn new_from_str(s: String) -> Self {
        let inputs: Vec<u8> = (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect();

        assert_eq!(inputs.len(), 213);
        let rounds: u32 = u32::from_be_bytes(inputs[0..4].try_into().unwrap());
        let h_vec_values: Vec<u64> = (0..H_LEN)
            .map(|i| u64::from_le_bytes(inputs[4 + i * 8..4 + (i + 1) * 8].try_into().unwrap()))
            .collect();

        let m_vec_values: Vec<u64> = (0..M_LEN)
            .map(|i| {
                u64::from_le_bytes(
                    inputs[4 + (H_LEN + i) * 8..4 + (H_LEN + i + 1) * 8]
                        .try_into()
                        .unwrap(),
                )
            })
            .collect();

        let iv_vec_values = IV_VALUES.to_vec();

        let mut v_vec_values = h_vec_values.clone();
        v_vec_values.append(&mut iv_vec_values.clone());

        let t_vec_values: Vec<u64> = (0..2)
            .map(|i| {
                u64::from_le_bytes(
                    inputs[4 + (H_LEN + M_LEN + i) * 8..4 + (H_LEN + M_LEN + i + 1) * 8]
                        .try_into()
                        .unwrap(),
                )
            })
            .collect();

        let f = inputs[4 + (H_LEN + M_LEN + 2) * 8];
        assert_eq!(f * (1 - f), 0);

        Self {
            h_vec_values,
            m_vec_values,
            v_vec_values,
            iv_vec_values,
            t_vec_values,
            f: f != 0,
            rounds,
        }
    }

    pub fn pre_input_gen<F: Field + Hash>(&mut self) -> PreInput<F> {
        let h_split_4bits_vec = split_to_4bits_values::<F>(&self.h_vec_values);
        let m_split_4bits_vec = split_to_4bits_values::<F>(&self.m_vec_values);
        let iv_split_4bits_vec: Vec<Vec<F>> = split_to_4bits_values::<F>(&self.iv_vec_values[4..7]);
        let t_split_4bits_vec = split_to_4bits_values::<F>(&self.t_vec_values);

        let final_values = vec![
            self.v_vec_values[12] ^ self.t_vec_values[0],
            self.v_vec_values[13] ^ self.t_vec_values[1],
            self.v_vec_values[14] ^ 0xFFFFFFFFFFFFFFFF,
        ];
        let final_split_bits_vec = split_to_4bits_values::<F>(&final_values);

        let pre_inputs = PreInput {
            round: F::ZERO,
            final_round: F::from(self.rounds as u64),
            t0: F::from(self.t_vec_values[0]),
            t1: F::from(self.t_vec_values[1]),
            f: F::from(if self.f { 1 } else { 0 }),
            h_vec: self.h_vec_values.iter().map(|&v| F::from(v)).collect(),
            m_vec: self.m_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_vec: self.v_vec_values.iter().map(|&v| F::from(v)).collect(),
            h_split_4bits_vec,
            m_split_4bits_vec,
            t_split_4bits_vec,
            iv_split_4bits_vec,
            final_split_bits_vec,
        };

        self.v_vec_values[12] = final_values[0];
        self.v_vec_values[13] = final_values[1];
        if self.f {
            self.v_vec_values[14] = final_values[2];
        }
        pre_inputs
    }

    pub fn g_step_gen<F: Field + Hash>(&mut self, r: u32) -> GInput<F> {
        let s = SIGMA_VALUES[(r as usize) % 10];

        let mut v_mid1_vec_values = self.v_vec_values.clone();
        let mut v_mid2_vec_values = self.v_vec_values.clone();
        let mut v_mid_va_bit_vec = Vec::new();
        let mut v_mid_vb_bit_vec = Vec::new();
        let mut v_mid_vc_bit_vec = Vec::new();
        let mut v_mid_vd_bit_vec = Vec::new();
        let mut v_xor_d_bit_vec = Vec::new();
        let mut v_xor_b_bit_vec = Vec::new();
        let mut b_bit_vec = Vec::new();
        let mut b_3bits_vec = Vec::new();

        g_wg(
            (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
            (0, 4, 8, 12),
            (self.m_vec_values[s[0]], self.m_vec_values[s[1]]),
            (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
            (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
            (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
            (&mut b_bit_vec, &mut b_3bits_vec),
        );
        g_wg(
            (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
            (1, 5, 9, 13),
            (self.m_vec_values[s[2]], self.m_vec_values[s[3]]),
            (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
            (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
            (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
            (&mut b_bit_vec, &mut b_3bits_vec),
        );
        g_wg(
            (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
            (2, 6, 10, 14),
            (self.m_vec_values[s[4]], self.m_vec_values[s[5]]),
            (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
            (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
            (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
            (&mut b_bit_vec, &mut b_3bits_vec),
        );
        g_wg(
            (&mut v_mid1_vec_values, &mut v_mid2_vec_values),
            (3, 7, 11, 15),
            (self.m_vec_values[s[6]], self.m_vec_values[s[7]]),
            (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
            (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
            (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
            (&mut b_bit_vec, &mut b_3bits_vec),
        );

        let mut v_mid3_vec_values = v_mid2_vec_values.clone();
        let mut v_mid4_vec_values = v_mid2_vec_values.clone();
        g_wg(
            (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
            (0, 5, 10, 15),
            (self.m_vec_values[s[8]], self.m_vec_values[s[9]]),
            (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
            (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
            (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
            (&mut b_bit_vec, &mut b_3bits_vec),
        );
        g_wg(
            (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
            (1, 6, 11, 12),
            (self.m_vec_values[s[10]], self.m_vec_values[s[11]]),
            (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
            (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
            (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
            (&mut b_bit_vec, &mut b_3bits_vec),
        );
        g_wg(
            (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
            (2, 7, 8, 13),
            (self.m_vec_values[s[12]], self.m_vec_values[s[13]]),
            (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
            (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
            (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
            (&mut b_bit_vec, &mut b_3bits_vec),
        );
        g_wg(
            (&mut v_mid3_vec_values, &mut v_mid4_vec_values),
            (3, 4, 9, 14),
            (self.m_vec_values[s[14]], self.m_vec_values[s[15]]),
            (&mut v_mid_va_bit_vec, &mut v_mid_vb_bit_vec),
            (&mut v_mid_vc_bit_vec, &mut v_mid_vd_bit_vec),
            (&mut v_xor_d_bit_vec, &mut v_xor_b_bit_vec),
            (&mut b_bit_vec, &mut b_3bits_vec),
        );

        let ginputs = GInput {
            round: F::from(r as u64),
            final_round: F::from(self.rounds as u64),
            v_vec: self.v_vec_values.iter().map(|&v| F::from(v)).collect(),
            h_vec: self.h_vec_values.iter().map(|&v| F::from(v)).collect(),
            m_vec: self.m_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_mid1_vec: v_mid1_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_mid2_vec: v_mid2_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_mid3_vec: v_mid3_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_mid4_vec: v_mid4_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_mid_va_bit_vec,
            v_mid_vb_bit_vec,
            v_mid_vc_bit_vec,
            v_mid_vd_bit_vec,
            v_xor_d_bit_vec,
            v_xor_b_bit_vec,
            b_bit_vec,
            b_3bits_vec,
        };

        self.v_vec_values = v_mid4_vec_values.clone();
        ginputs
    }

    pub fn final_input_gen<F: Field + Hash>(&mut self) -> (FinalInput<F>, Vec<u64>) {
        let output_vec_values: Vec<u64> = self
            .h_vec_values
            .iter()
            .zip(
                self.v_vec_values[0..8]
                    .iter()
                    .zip(self.v_vec_values[V_LEN / 2..V_LEN].iter()),
            )
            .map(|(h, (v1, v2))| h ^ v1 ^ v2)
            .collect();

        let final_inputs = FinalInput {
            round: F::from(self.rounds as u64),
            final_round: F::from(self.rounds as u64),
            v_vec: self.v_vec_values.iter().map(|&v| F::from(v)).collect(),
            h_vec: self.h_vec_values.iter().map(|&v| F::from(v)).collect(),
            output_vec: output_vec_values.iter().map(|&v| F::from(v)).collect(),
            v_split_bit_vec: self
                .v_vec_values
                .iter()
                .map(|&v| split_value_4bits(v as u128, SPLIT_64BITS))
                .collect(),
            h_split_bit_vec: self
                .h_vec_values
                .iter()
                .map(|&v| split_value_4bits(v as u128, SPLIT_64BITS))
                .collect(),
            v_xor_split_bit_vec: self.v_vec_values[0..V_LEN / 2]
                .iter()
                .zip(self.v_vec_values[V_LEN / 2..V_LEN].iter())
                .map(|(&v1, &v2)| split_xor_value(v1, v2))
                .collect(),
            final_split_bit_vec: output_vec_values
                .iter()
                .map(|&output| split_value_4bits(output as u128, SPLIT_64BITS))
                .collect(),
        };
        (final_inputs, output_vec_values)
    }
}

pub struct PreInput<F> {
    pub round: F,
    pub final_round: F,
    pub t0: F,
    pub t1: F,
    pub f: F,
    pub v_vec: Vec<F>,
    pub h_vec: Vec<F>,
    pub m_vec: Vec<F>,
    pub h_split_4bits_vec: Vec<Vec<F>>,
    pub m_split_4bits_vec: Vec<Vec<F>>,
    pub t_split_4bits_vec: Vec<Vec<F>>,
    pub iv_split_4bits_vec: Vec<Vec<F>>,
    pub final_split_bits_vec: Vec<Vec<F>>,
}

pub struct GInput<F> {
    pub round: F,
    pub final_round: F,
    pub v_vec: Vec<F>,
    pub h_vec: Vec<F>,
    pub m_vec: Vec<F>,
    pub v_mid1_vec: Vec<F>,
    pub v_mid2_vec: Vec<F>,
    pub v_mid3_vec: Vec<F>,
    pub v_mid4_vec: Vec<F>,
    pub v_mid_va_bit_vec: Vec<Vec<F>>,
    pub v_mid_vb_bit_vec: Vec<Vec<F>>,
    pub v_mid_vc_bit_vec: Vec<Vec<F>>,
    pub v_mid_vd_bit_vec: Vec<Vec<F>>,
    pub v_xor_d_bit_vec: Vec<Vec<F>>,
    pub v_xor_b_bit_vec: Vec<Vec<F>>,
    pub b_bit_vec: Vec<F>,
    pub b_3bits_vec: Vec<F>,
}

pub struct FinalInput<F> {
    pub round: F,
    pub final_round: F,
    pub v_vec: Vec<F>,
    pub h_vec: Vec<F>,
    pub output_vec: Vec<F>,
    pub v_split_bit_vec: Vec<Vec<F>>,
    pub h_split_bit_vec: Vec<Vec<F>>,
    pub v_xor_split_bit_vec: Vec<Vec<F>>,
    pub final_split_bit_vec: Vec<Vec<F>>,
}

fn split_xor_value<F: Field + Hash>(value1: u64, value2: u64) -> Vec<F> {
    let mut value1 = value1;
    let mut value2 = value2;
    let bit_values: Vec<u64> = (0..64)
        .map(|_| {
            let b1 = value1 % 2;
            value1 /= 2;
            let b2 = value2 % 2;
            value2 /= 2;
            b1 ^ b2
        })
        .collect();
    (0..SPLIT_64BITS as usize)
        .map(|i| {
            F::from(
                bit_values[i * 4]
                    + bit_values[i * 4 + 1] * 2
                    + bit_values[i * 4 + 2] * 4
                    + bit_values[i * 4 + 3] * 8,
            )
        })
        .collect()
}

pub fn split_value_4bits<F: Field + Hash>(mut value: u128, n: u64) -> Vec<F> {
    (0..n)
        .map(|_| {
            let v = value % BASE_4BITS as u128;
            value /= BASE_4BITS as u128;

            F::from(v as u64)
        })
        .collect()
}

pub fn split_to_4bits_values<F: Field + Hash>(vec_values: &[u64]) -> Vec<Vec<F>> {
    vec_values
        .iter()
        .map(|&value| {
            let mut value = value;
            (0..SPLIT_64BITS)
                .map(|_| {
                    let v = value % BASE_4BITS;
                    value >>= 4;
                    F::from(v)
                })
                .collect()
        })
        .collect()
}

pub fn g_wg<F: Field + Hash>(
    (v1_vec_values, v2_vec_values): (&mut [u64], &mut [u64]),
    (a, b, c, d): (usize, usize, usize, usize),
    (x, y): (u64, u64),
    (va_bit_vec, vb_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (vc_bit_vec, vd_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (v_xor_d_bit_vec, v_xor_b_bit_vec): (&mut Vec<Vec<F>>, &mut Vec<Vec<F>>),
    (b_bit_vec, b_3bits_vec): (&mut Vec<F>, &mut Vec<F>),
) {
    va_bit_vec.push(split_value_4bits(
        v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + x as u128,
        SPLIT_64BITS + 1,
    ));
    v1_vec_values[a] = (v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + x as u128) as u64;

    vd_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, SPLIT_64BITS));
    v1_vec_values[d] = ((v1_vec_values[d] ^ v1_vec_values[a]) >> R1)
        ^ (v1_vec_values[d] ^ v1_vec_values[a]) << (64 - R1);
    v_xor_d_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, SPLIT_64BITS));

    vc_bit_vec.push(split_value_4bits(
        v1_vec_values[c] as u128 + v1_vec_values[d] as u128,
        SPLIT_64BITS + 1,
    ));
    v1_vec_values[c] = (v1_vec_values[c] as u128 + v1_vec_values[d] as u128) as u64;

    vb_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, SPLIT_64BITS));
    v1_vec_values[b] = ((v1_vec_values[b] ^ v1_vec_values[c]) >> R2)
        ^ (v1_vec_values[b] ^ v1_vec_values[c]) << (64 - R2);
    v_xor_b_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, SPLIT_64BITS));

    va_bit_vec.push(split_value_4bits(
        v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + y as u128,
        SPLIT_64BITS + 1,
    ));
    v2_vec_values[a] = (v1_vec_values[a] as u128 + v1_vec_values[b] as u128 + y as u128) as u64;

    vd_bit_vec.push(split_value_4bits(v1_vec_values[d] as u128, SPLIT_64BITS));
    v2_vec_values[d] = ((v1_vec_values[d] ^ v2_vec_values[a]) >> R3)
        ^ (v1_vec_values[d] ^ v2_vec_values[a]) << (64 - R3);
    v_xor_d_bit_vec.push(split_value_4bits(v2_vec_values[d] as u128, SPLIT_64BITS));

    vc_bit_vec.push(split_value_4bits(
        v1_vec_values[c] as u128 + v2_vec_values[d] as u128,
        SPLIT_64BITS + 1,
    ));
    v2_vec_values[c] = (v1_vec_values[c] as u128 + v2_vec_values[d] as u128) as u64;

    vb_bit_vec.push(split_value_4bits(v1_vec_values[b] as u128, SPLIT_64BITS));
    v2_vec_values[b] = ((v1_vec_values[b] ^ v2_vec_values[c]) >> R4)
        ^ (v1_vec_values[b] ^ v2_vec_values[c]) << (64 - R4);
    v_xor_b_bit_vec.push(split_value_4bits(
        (v1_vec_values[b] ^ v2_vec_values[c]) as u128,
        SPLIT_64BITS,
    ));
    let bits = (v1_vec_values[b] ^ v2_vec_values[c]) / 2u64.pow(60);
    b_bit_vec.push(F::from(bits / 8));
    b_3bits_vec.push(F::from(bits % 8))
}
