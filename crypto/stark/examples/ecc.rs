use env_logger;
use log::info;
use std::time::Instant;
use zkp_macros_decl::field_element;
use zkp_primefield::{FieldElement, Root, SquareInline, One};
use zkp_stark::{Constraints, Provable, RationalExpression, TraceTable, Verifiable};
use zkp_u256::U256;
use zkp_elliptic_curve::BETA;


struct PointOnCurveClaim {
    x : FieldElement,
    y : FieldElement,
    // nebo u, v v Edwardsove forme?
}

impl Verifiable for PointOnCurveClaim{
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;

        // Seed
        // let mut seed = (self.x + self.y).clone().as_montgomery().to_bytes_be().to_vec();

        // y*y ==? x*x*x + x + BETA
        Constraints::from_expressions((2, 2), self.x.as_montgomery().to_bytes_be().to_vec(), vec![
            (Trace(0, 0) - &self.x) / (X - 1),
            (Trace(1, 0) - &self.y) / (X - 1),
            (Trace(1, 0)*Trace(1, 0) - Trace(0, 0)*Trace(0, 0)*Trace(0, 0)*Trace(0, 0) - Trace(0, 0) - Constant(BETA)) / (X - 1)
        ])
            .unwrap()
    }
}

impl Provable<&FieldElement> for PointOnCurveClaim{
    fn trace(&self, witness: &FieldElement) -> TraceTable {
        let mut trace = TraceTable::new(2, 2);
        trace[(0, 0)] = self.x.clone();
        trace[(0, 1)] = self.y.clone();
        trace
    }
}

struct NoSmallOrderPointClaim {
    x : FieldElement,
    y : FieldElement,
    //nebo  u, v ?
}

#[derive(Clone, Debug)]
struct NDoublingPointClaim {
    x_start : FieldElement,
    y_start : FieldElement,
    x_result : FieldElement,
    y_result : FieldElement,
    index : usize,
}

impl Verifiable for NDoublingPointClaim{
    // assuming y is not zero
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;

        // Seed
        let mut seed = self.index.to_be_bytes().to_vec();
        seed.extend_from_slice(&self.x_start.as_montgomery().to_bytes_be());
        seed.extend_from_slice(&self.y_start.as_montgomery().to_bytes_be());

        // Constraint repetitions
        let trace_length = (self.index+1).next_power_of_two();
        let trace_generator = FieldElement::root(trace_length).unwrap();
        let g = Constant(trace_generator);
        let on_row = |index| (X - g.pow(index)).inv();
        let every_row = || (X - g.pow(trace_length - 1)) / (X.pow(trace_length) - 1);

        let m_trace : RationalExpression =  ((Trace(0,0) + Trace(0,0) + Trace(0,0)) * Trace(0,0) + Constant(FieldElement::one()) ) / ( Trace(1,0) + Trace(1,0));

        Constraints::from_expressions((trace_length, 4), seed, vec![
            // Boundary Constraints
            (Trace(0, 0) - &self.x_start) * on_row(0),
            (Trace(1, 0) - &self.y_start) * on_row(0),
            (Trace(0, 0) - &self.x_result) * on_row(self.index),
            (Trace(1, 0) - &self.y_result) * on_row(self.index),

            // check that result of each row is "previous" on  the next row
            (Trace(2, 0) - Trace(0, 1)) * every_row(),
            (Trace(3, 0) - Trace(1, 1)) * every_row(),

            // check the doubling steps
            // let m = ((x + x + x) * x + FieldElement::one()) / (y + y);
            // trace[(i, 2)] = &m * &m - x - x;
            // trace[(i, 3)] = m * (x - &trace[(i, 2)]) - y;
            // Trace(0,0) * every_row(), ok
            // Trace(1,0) * every_row(), ok
            // Trace(2, 0) * every_row(), ok
            // Trace(3, 0) * every_row(), ok
            // Trace(0, 1) * every_row(),
            // Trace(1, 1) * every_row(),
            m_trace.clone(),
            m_trace.clone() * m_trace.clone() - Trace(0, 0) - Trace(0, 0),
            (m_trace.clone() * m_trace.clone() - Trace(0, 0) - Trace(0, 0)  - Trace(0, 1) ) * every_row(),
            (m_trace.clone() * ( Trace(0, 0) - Trace(0, 1)) - Trace(1, 0) - Trace(1, 1)) * every_row(),
        ])
            .unwrap()
    }
}
#[derive(Clone, Debug)]
struct Witness {
    secret: FieldElement,
}

impl Provable<&Witness> for NDoublingPointClaim{
    // assuming y is not zero
    fn trace(&self, witness: &Witness) -> TraceTable {
        let trace_length = (self.index+1).next_power_of_two();
        // let trace_length = self.index+1;
        let mut trace = TraceTable::new(trace_length, 4);

        // let m = ((x + x + x) * x + FieldElement::one()) / (y + y);
        // let nx = &m * &m - x - x;
        // let ny = m * (x - &nx) - y;

        let mut prev_c0 = self.x_start.clone();
        let mut prev_c1 = self.y_start.clone();

        // trace[(0, 0)] = prev_c0.clone();
        // trace[(0, 1)] = prev_c1.clone();
        //
        // // dummy values
        // trace[(0, 2)] = prev_c0.clone();
        // trace[(0, 3)] = prev_c1.clone();

        for i in 0..(trace_length) {
            trace[(i, 0)] = prev_c0.clone();
            trace[(i, 1)] = prev_c1.clone();

            let x = &trace[(i, 0)].clone();
            let y = &trace[(i, 1)].clone();
            let m = ((x + x + x) * x + FieldElement::one()) / (y + y);
            info!("m is {:?}", &m);
            trace[(i, 2)] = &m * &m - x - x;
            trace[(i, 3)] = m * (x - &trace[(i, 2)]) - y;
            info!("Trace {:?}, 0: {:?}", i, trace[(i, 0)]);
            info!("Trace {:?}, 1: {:?}", i, trace[(i, 1)]);
            info!("Trace {:?}, 2: {:?}", i, trace[(i, 2)]);
            info!("Trace {:?}, 3: {:?}", i, trace[(i, 3)]);

            prev_c0 = trace[(i, 2)].clone();
            prev_c1 = trace[(i, 3)].clone();
        }
        trace
    }
}

// TODO
struct NMultiplicationPointClaim {
    x_start : FieldElement,
    y_start : FieldElement,
    x_result : FieldElement,
    y_result : FieldElement,
    index : usize,
}

// impl Verifiable for NMultiplicationPointClaim{
//     fn constraints(&self) -> Constraints {
//         use RationalExpression::*;
//     }
// }


// impl Provable<&Witness> for NMultiplicationPointClaim{
//     fn trace(&self, witness: &Witness) -> TraceTable {
//         }
//     }
// }

fn main() {
    env_logger::init();

    // From algebra/elliptic-curve/src/curve.rs test_double
    info!("Constructing claim");
    let claim = NDoublingPointClaim {
        x_start: field_element!("01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca"),
        y_start: field_element!("005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f"),

        // n = 1
        // x_result: field_element!("0759ca09377679ecd535a81e83039658bf40959283187c654c5416f439403cf5"),
        // y_result: field_element!("06f524a3400e7708d5c01a28598ad272e7455aa88778b19f93b562d7a9646c41"),
        // index: 1,

        // n = 2
        x_result: field_element!("a7da05a4d664859ccd6e567b935cdfbfe3018c7771cb980892ef38878ae9bc"),
        y_result: field_element!("0584b0c2bc833a4c88d62b387e0ef868cae2eaaa288f4ca7b34c84b46ca031b6"),
        index: 2,


        // n = 3
        // x_result: field_element!("06eeee2b0c71d681692559735e08a2c3ba04e7347c0c18d4d49b83bb89771591"),
        // y_result: field_element!("072498c69f16e02231e26a6a6acaabb8714e0af1306066231dd38c233ee15216"),
        // index: 3,

        // n = 4
        // x_result: field_element!("b582a82e6c8ad99e38fcbd2a4da97b37d0cdb7d776edb84a661d79ec4824ac"),
        // y_result: field_element!("07cf4349849204906e1b19538552fcb1565171ab453694b574c87e2a35206d9c"),
        // index: 4,

        // n = 5
        // x_result: field_element!("045f571e26cc38d3e6fdce1b659350f93e272cac9834b78eb8681f7ef89239aa"),
        // y_result: field_element!("05abd8de04bd2c3b7890082929fcd2e1aa252e9508f39e19637456eb1d7cc493"),
        // index: 5,

        //
        // 6 :
        // 0x6c4d7eb804667b5c86b09dd6ad31a554a0f4798cb529eed1615c8c1666cff8e
        // 0x605aa7ed522042afe5c9070a71cdf26510758ef847fa4600e7952ae7ec5d536
        //
        //
        // 7 :
        // 0x3455359ce0517acec33aed439350e69dd854d6c689dcce27285e5e262806abc
        // 0x3049f60eb15d1da1c32fc196d0ca814fae84bc3a6890716edbbdbe1038e35ea
        //
        //
        // 8 :
        // 0x6d840e6d0ecfcbcfa83c0f704439e16c69383d93f51427feb9a4f2d21fbe075
        // 0x58f7ce5eb6eb5bd24f70394622b1f4d2c54ebca317a3e61bf9f349dccf166cf

    };
    info!("Claim: {:?}", claim);

    info!("Constructing witness");
    let witness = Witness {
        secret: field_element!("cafebabe"),
    };
    info!("Witness: {:?}", witness);

    assert_eq!(claim.check(&witness), Ok(()));

    // Start timer
    let start = Instant::now();

    info!("Constructing proof...");
    let _proof = claim.prove(&witness).unwrap();

    // Measure time
    let duration = start.elapsed();
    info!("Time elapsed in proof function is: {:?}", duration);
}