#![warn(clippy::all)]
use env_logger;
use log::info;
use std::time::Instant;
use zkp_macros_decl::field_element;
use zkp_primefield::{FieldElement, Root, One};
use zkp_stark::{Constraints, Provable, RationalExpression, TraceTable, Verifiable};
use zkp_u256::U256;

#[derive(Clone, Debug)]
struct Claim {
    index: usize,
    value: FieldElement,
}

#[derive(Clone, Debug)]
struct Witness {
    secret: FieldElement,
}

impl Verifiable for Claim {
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;

        // Seed
        let mut seed = self.index.to_be_bytes().to_vec();
        seed.extend_from_slice(&self.value.as_montgomery().to_bytes_be());

        // Constraint repetitions
        let trace_length = self.index.next_power_of_two();
        let trace_generator = FieldElement::root(trace_length).unwrap();
        let g = Constant(trace_generator);
        let on_row = |index| (X - g.pow(index)).inv();
        let every_row = || (X - g.pow(trace_length - 1)) / (X.pow(trace_length) - 1);

        Constraints::from_expressions((trace_length, 2), seed, vec![
            (Trace(0, 1) - Trace(1, 0)) * every_row(),
            (Trace(1, 1) - Trace(0, 0) - Trace(1, 0)) * every_row(),
            (Trace(0, 0) - 1) * on_row(0),
            (Trace(0, 0) - &self.value) * on_row(self.index),
        ])
            .unwrap()
    }
}

impl Provable<&Witness> for Claim {
    fn trace(&self, witness: &Witness) -> TraceTable {
        let trace_length = self.index.next_power_of_two();
        let mut trace = TraceTable::new(trace_length, 2);
        trace[(0, 0)] = 1.into();
        trace[(0, 1)] = witness.secret.clone();
        for i in 0..(trace_length - 1) {
            trace[(i + 1, 0)] = trace[(i, 1)].clone();
            trace[(i + 1, 1)] = &trace[(i, 0)] + &trace[(i, 1)];
        }
        trace
    }
}

fn main() {
    env_logger::init();

    info!("Constructing claim");
    let claim = Claim {
        // index: 1000,
        // value: field_element!("0142c45e5d743d10eae7ebb70f1526c65de7dbcdb65b322b6ddc36a812591e8f"),
        index : 2,
        value: field_element!("01")
    };
    info!("Claim: {:?}", claim);

    info!("Constructing witness");
    let witness = Witness {
        // secret: field_element!("cafebabe"),
        secret: field_element!("00"),
    };
    info!("Witness: {:?}", witness);

    let mut cx = FieldElement::one();
    for n in 1..1001 {
        let claim2 = Claim {
            index: 5,
            value: cx.clone(),  // or: FieldElement::from_uint(&U256::from(n))
        };
        if claim2.check(&witness) == Ok(()) {
            println!("Found the match {:?}, {:?}", n, cx);
            break;
        }
        cx += FieldElement::one();
    }

    assert_eq!(claim.check(&witness), Ok(()));

    // Start timer
    let start = Instant::now();

    info!("Constructing proof...");
    let _proof = claim.prove(&witness).unwrap();

    // Measure time
    let duration = start.elapsed();
    info!("Time elapsed in proof function is: {:?}", duration);
}
