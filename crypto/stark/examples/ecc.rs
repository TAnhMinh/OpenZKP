use env_logger;
use log::info;
use std::time::Instant;
use zkp_macros_decl::field_element;
use zkp_primefield::{FieldElement, Root, SquareInline, One, Zero, PrimeField};
use zkp_stark::{Constraints, Provable, RationalExpression, TraceTable, Verifiable};
use zkp_u256::U256;
use zkp_elliptic_curve::{BETA, ScalarFieldElement};
use zkp_primefield::u256::Binary;
use std::borrow::Borrow;
//use zkp_primefield::u256::Binary;
//use zkp_primefield::u256::Binary;

#[derive(Clone, Debug)]
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
            (Trace(1, 0)*Trace(1, 0)
                - Trace(0, 0)*Trace(0, 0)*Trace(0, 0) - Trace(0, 0) - Constant(BETA)) / (X - 1)
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

        Constraints::from_expressions((trace_length, 7), seed, vec![
            // Boundary Constraints
            (Trace(0, 0) - &self.x_start) * on_row(0),
            (Trace(1, 0) - &self.y_start) * on_row(0),
            (Trace(0, 0) - &self.x_result) * on_row(self.index),
            (Trace(1, 0) - &self.y_result) * on_row(self.index),

            // check that result of each row is "previous" on  the next row
            (Trace(5, 0) - Trace(0, 1)) * every_row(),
            (Trace(6, 0) - Trace(1, 1)) * every_row(),

            // m_denominator (citatel)
            ((Trace(0,0) + Trace(0,0) + Trace(0,0)) * Trace(0,0) + Constant(FieldElement::one())
                - Trace(2, 0)) * every_row(),
            // m_nominator (jmenovatel)
            (Trace(3, 0) - (Trace(1, 0) + Trace(1, 0))) * every_row(),
            // m
            (Trace(4, 0) * Trace(3, 0) - Trace(2, 0)) * every_row(),
            // trace[(i, 5)] = &m * &m - x - x; ... new x
            (Trace(4, 0) * Trace(4, 0) - Trace(0,0) - Trace(0, 0)
                - Trace(5, 0)) * every_row(),
            // trace[(i, 6)] = m * (x - &trace[(i, 5)]) - y; ... new y
            (Trace(4, 0) * (Trace(0,0)  - Trace(5, 0)) - Trace(1, 0)
                - Trace(6, 0)) * every_row(),

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
        let mut trace = TraceTable::new(trace_length, 7);

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
            // info!("m is {:?}", &m);
            trace[(i, 2)] = (x + x + x) * x + FieldElement::one();
            trace[(i, 3)] = y + y;
            trace[(i, 4)] = m.clone();
            trace[(i, 5)] = m.clone() * m.clone() - x - x;
            trace[(i, 6)] = m.clone() * (x - &trace[(i, 5)]) - y;
            info!("Trace {:?}, 0: {:?}", i, trace[(i, 0)]);
            info!("Trace {:?}, 1: {:?}", i, trace[(i, 1)]);
            info!("Trace {:?}, 2: {:?}", i, trace[(i, 2)]);
            info!("Trace {:?}, 3: {:?}", i, trace[(i, 3)]);
            info!("Trace {:?}, 4: {:?}", i, trace[(i, 4)]);
            info!("Trace {:?}, 5: {:?}", i, trace[(i, 5)]);
            info!("Trace {:?}, 6: {:?}", i, trace[(i, 6)]);


            prev_c0 = trace[(i, 5)].clone();
            prev_c1 = trace[(i, 6)].clone();
        }
        trace
    }
}

//TODO
// #[derive(Clone, Debug)]
// struct MultiplicationPointClaim {
//     x_start : FieldElement,
//     y_start : FieldElement,
//     x_result : FieldElement,
//     y_result : FieldElement,
//
//     //scalar
//     scalar : ScalarFieldElement,
// }
//
// impl Verifiable for MultiplicationPointClaim{
//     // assuming y is not zero
//     fn constraints(&self) -> Constraints {
//         use RationalExpression::*;
//
//         // Seed
//         let mut seed = self.scalar.to_be_bytes().to_vec();
//         //self.index.to_be_bytes().to_vec();
//         seed.extend_from_slice(&self.x_start.as_montgomery().to_bytes_be());
//         seed.extend_from_slice(&self.y_start.as_montgomery().to_bytes_be());
//
//         // Constraint repetitions
//         let trace_length = (self.index+1).next_power_of_two();
//         let trace_generator = FieldElement::root(trace_length).unwrap();
//         let g = Constant(trace_generator);
//         let on_row = |index| (X - g.pow(index)).inv();
//         let every_row = || (X - g.pow(trace_length - 1)) / (X.pow(trace_length) - 1);
//
//         let m_trace : RationalExpression =  ((Trace(0,0) + Trace(0,0) + Trace(0,0)) * Trace(0,0) + Constant(FieldElement::one()) ) / ( Trace(1,0) + Trace(1,0));
//
//         Constraints::from_expressions((trace_length, 7), seed, vec![
//             // Boundary Constraints
//             (Trace(0, 0) - &self.x_start) * on_row(0),
//             (Trace(1, 0) - &self.y_start) * on_row(0),
//             (Trace(0, 0) - &self.x_result) * on_row(self.index),
//             (Trace(1, 0) - &self.y_result) * on_row(self.index),
//
//             // check that result of each row is "previous" on  the next row
//             (Trace(5, 0) - Trace(0, 1)) * every_row(),
//             (Trace(6, 0) - Trace(1, 1)) * every_row(),
//
//             // m_denominator (citatel)
//             ((Trace(0,0) + Trace(0,0) + Trace(0,0)) * Trace(0,0) + Constant(FieldElement::one())
//                 - Trace(2, 0)) * every_row(),
//             // m_nominator (jmenovatel)
//             (Trace(3, 0) - (Trace(1, 0) + Trace(1, 0))) * every_row(),
//             // m
//             (Trace(4, 0) * Trace(3, 0) - Trace(2, 0)) * every_row(),
//             // trace[(i, 5)] = &m * &m - x - x; ... new x
//             (Trace(4, 0) * Trace(4, 0) - Trace(0,0) - Trace(0, 0)
//                 - Trace(5, 0)) * every_row(),
//             // trace[(i, 6)] = m * (x - &trace[(i, 5)]) - y; ... new y
//             (Trace(4, 0) * (Trace(0,0)  - Trace(5, 0)) - Trace(1, 0)
//                 - Trace(6, 0)) * every_row(),
//
//         ])
//             .unwrap()
//     }
// }
//
#[derive(Clone, Debug)]
struct WitnessMul {
    x_start : FieldElement,
    y_start : FieldElement,
    scalar: ScalarFieldElement,
    //scalar: ScalarFieldElement
    //Note: scalar.bin(i) = i-th LSB
}
//
//
// according to https://github.com/GuildOfWeavers/genSTARK/blob/master/examples/elliptic/pointmul.aa
// impl Provable<&WitnessMul> for MultiplicationPointClaim{
//     fn trace(&self, witness: &WitnessMul) -> TraceTable {
//         //256 bit scalar
//         let trace_length = 256;
//         let mut trace = TraceTable::new(trace_length, 13);
//
//         let mut prev_s0 = witness.x_start.clone();
//         let mut prev_s1 = witness.y_start.clone();
//
//
//         // trace[(0, 0)] = prev_c0.clone();
//         // trace[(0, 1)] = prev_c1.clone();
//         //
//         // // dummy values
//         // trace[(0, 2)] = prev_c0.clone();
//         // trace[(0, 3)] = prev_c1.clone();
//
//         // Setting public register, ~ initTrace
//
//         for i in 0..(trace_length) {
//             // Private registers (5)
//             trace[(i, 0)] = prev_c0.clone();
//             trace[(i, 1)] = prev_c1.clone();
//             trace[(i, 2)] = witness.scalar.bin(i);
//             trace[(i, 3)] = field_element!("00"); //?? mask
//             trace[(i, 4)] = 2.pow(i as u32).into();
//
//             info!("Trace {:?}, 0: {:?}", i, trace[(i, 0)]);
//             info!("Trace {:?}, 1: {:?}", i, trace[(i, 1)]);
//             info!("Trace {:?}, 2: {:?}", i, trace[(i, 2)]);
//             info!("Trace {:?}, 3: {:?}", i, trace[(i, 3)]);
//             info!("Trace {:?}, 4: {:?}", i, trace[(i, 4)]);
//
//             // Public registers (8)
//
//             // prev_c0 = trace[(i, 5)].clone();
//             // prev_c1 = trace[(i, 6)].clone();
//         }
//         trace
//     }
// }


fn main() {
    //n_doubling_construction();
    // point_on_curve_construction();
    let x = format!("{:x}", 2_i32.pow(5));
    assert_eq!(x, "20");
    let fe : FieldElement = 2_i32.pow(5).into();
    println!("{}", x);
    println!("{:?}", fe);

    let witness = WitnessMul  {
        x_start : 2.into(),
        y_start : 4.into(),
        scalar : 13.into()

    };

    // let trace_length = 256;
    let trace_length = 4;
    let mut trace = TraceTable::new(trace_length, 13);

    let mut prev_s0 = witness.x_start.clone();
    let mut prev_s1 = witness.y_start.clone();

    // implementing the setup for first row of public columns
    // corresponds to initTrace in https://github.com/GuildOfWeavers/genSTARK/blob/master/examples/elliptic/pointmul.aa
    let mut pub_array_row : Vec<FieldElement> = vec![];

    let m1 = computeM1(prev_s0.borrow(), prev_s1.borrow());

    pub_array_row.push(witness.x_start.clone());
    pub_array_row.push(witness.y_start.clone());
    pub_array_row.push(FieldElement::zero());
    pub_array_row.push(FieldElement::zero());
    pub_array_row.push(m1);
    pub_array_row.push(FieldElement::zero());
    pub_array_row.push(1.into());
    pub_array_row.push(FieldElement::zero());

    // for i in 0..8{
    //     println!("Init pub row {}: {:?}", i, pub_array_row[i]);
    // }

    // Writing into the private columns (5 columns)
    for i in 0..(trace_length) {
        // Private registers (5 columns)
        trace[(i, 0)] = prev_s0.clone(); //?? not sure
        trace[(i, 1)] = prev_s1.clone(); //?? not sure yet
        let aux : i32 = witness.scalar.to_uint().bit(i).into();
        trace[(i, 2)] = aux.into();
        trace[(i, 3)] = field_element!("00"); //?? mask
        trace[(i, 4)] = 2_i32.pow(i as u32).into();

        println!("Trace {:?}, 0: {:?}", i, trace[(i, 0)]);
        println!("Trace {:?}, 1: {:?}", i, trace[(i, 1)]);
        println!("Trace {:?}, 2: {:?}", i, trace[(i, 2)]);
        println!("Trace {:?}, 3: {:?}", i, trace[(i, 3)]);
        println!("Trace {:?}, 4: {:?}", i, trace[(i, 4)]);

        // Public registers (8 columns)


        // prev_c0 = trace[(i, 5)].clone();
        // prev_c1 = trace[(i, 6)].clone();
    }

    // Writing into public columns (8 columns)

}

fn computeM1(x : &FieldElement, y: &FieldElement)->FieldElement{
    // println!("x: {:?}", x);
    // println!("y: {:?}", y);
    let mut m : FieldElement = (x + x + x) * x + &1.into();
    // println!("m: {:?}", m);
    m = m / (y + y);
    // println!("m final: {:?}", m);
    m
}


fn n_doubling_construction(){
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
        // x_result: field_element!("a7da05a4d664859ccd6e567b935cdfbfe3018c7771cb980892ef38878ae9bc"),
        // y_result: field_element!("0584b0c2bc833a4c88d62b387e0ef868cae2eaaa288f4ca7b34c84b46ca031b6"),
        // index: 2,


        // n = 3
        // x_result: field_element!("06eeee2b0c71d681692559735e08a2c3ba04e7347c0c18d4d49b83bb89771591"),
        // y_result: field_element!("072498c69f16e02231e26a6a6acaabb8714e0af1306066231dd38c233ee15216"),
        // index: 3,

        // n = 4
        // x_result: field_element!("b582a82e6c8ad99e38fcbd2a4da97b37d0cdb7d776edb84a661d79ec4824ac"),
        // y_result: field_element!("07cf4349849204906e1b19538552fcb1565171ab453694b574c87e2a35206d9c"),
        // index: 4,

        // n = 5
        x_result: field_element!("045f571e26cc38d3e6fdce1b659350f93e272cac9834b78eb8681f7ef89239aa"),
        y_result: field_element!("05abd8de04bd2c3b7890082929fcd2e1aa252e9508f39e19637456eb1d7cc493"),
        index: 5,

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

fn point_on_curve_construction(){
    env_logger::init();

    // From algebra/elliptic-curve/src/curve.rs test_double
    info!("Constructing claim");
    let claim = PointOnCurveClaim {
        // x: field_element!("01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca"),
        // y: field_element!("005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f")

        // x: field_element!("0759ca09377679ecd535a81e83039658bf40959283187c654c5416f439403cf5"),
        // y: field_element!("06f524a3400e7708d5c01a28598ad272e7455aa88778b19f93b562d7a9646c41"),

        // x: field_element!("a7da05a4d664859ccd6e567b935cdfbfe3018c7771cb980892ef38878ae9bc"),
        // y: field_element!("0584b0c2bc833a4c88d62b387e0ef868cae2eaaa288f4ca7b34c84b46ca031b6"),

        // x: field_element!("06eeee2b0c71d681692559735e08a2c3ba04e7347c0c18d4d49b83bb89771591"),
        // y: field_element!("072498c69f16e02231e26a6a6acaabb8714e0af1306066231dd38c233ee15216"),

        // x: field_element!("b582a82e6c8ad99e38fcbd2a4da97b37d0cdb7d776edb84a661d79ec4824ac"),
        // y: field_element!("07cf4349849204906e1b19538552fcb1565171ab453694b574c87e2a35206d9c"),

        // x: field_element!("045f571e26cc38d3e6fdce1b659350f93e272cac9834b78eb8681f7ef89239aa"),
        // y: field_element!("05abd8de04bd2c3b7890082929fcd2e1aa252e9508f39e19637456eb1d7cc493"),

        // x: field_element!("06c4d7eb804667b5c86b09dd6ad31a554a0f4798cb529eed1615c8c1666cff8e"),
        // y: field_element!("0605aa7ed522042afe5c9070a71cdf26510758ef847fa4600e7952ae7ec5d536"),

        // x: field_element!("03455359ce0517acec33aed439350e69dd854d6c689dcce27285e5e262806abc"),
        // y: field_element!("03049f60eb15d1da1c32fc196d0ca814fae84bc3a6890716edbbdbe1038e35ea"),

        x: field_element!("06d840e6d0ecfcbcfa83c0f704439e16c69383d93f51427feb9a4f2d21fbe075"),
        y: field_element!("058f7ce5eb6eb5bd24f70394622b1f4d2c54ebca317a3e61bf9f349dccf166cf"),
    };


    info!("Claim: {:?}", claim);

    //only a "dummy" witness, FieldElement::zero()

    assert_eq!(claim.check(&FieldElement::zero()), Ok(()));

    // Start timer
    let start = Instant::now();

    info!("Constructing proof...");
    let _proof = claim.prove(&FieldElement::zero()).unwrap();

    // Measure time
    let duration = start.elapsed();
    info!("Time elapsed in proof function is: {:?}", duration);

}