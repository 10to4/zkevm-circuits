use super::circuit::Blake2fCircuit;
use eth_types::Field;
use halo2_proofs::dev::MockProver;

pub fn string_to_u64(inputs: [&str; 4]) -> [u64; 4] {
    inputs
        .iter()
        .map(|&input| {
            assert_eq!(16, input.len());
            u64::from_le_bytes(
                (0..input.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&input[i..i + 2], 16).unwrap())
                    .collect::<Vec<u8>>()
                    .try_into()
                    .unwrap(),
            )
        })
        .collect::<Vec<u64>>()
        .try_into()
        .unwrap()
}

fn test_blake2f_circuit<F: Field>(inputs: &[Vec<u8>]) {
    let circuit = Blake2fCircuit::<F>::new(inputs);
    let prover = MockProver::run(9, &circuit, Vec::new()).unwrap();
    let result = prover.verify_par();
    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}

#[test]
fn test_blake2f_example() {
    use halo2_proofs::halo2curves::bn256::Fr;

    let s = String::from("0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001");

    let v = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect();

    test_blake2f_circuit::<Fr>(&[v]);
}
