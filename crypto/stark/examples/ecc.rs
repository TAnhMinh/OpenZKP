use env_logger;
use log::info;
use std::time::Instant;
use zkp_macros_decl::field_element;
use zkp_macros_decl::u256h;
use zkp_primefield::{FieldElement, Root, SquareInline, One, Zero, PrimeField};
use zkp_stark::{Constraints, Provable, RationalExpression, TraceTable, Verifiable};
use zkp_u256::U256;
use zkp_elliptic_curve::{BETA, ScalarFieldElement, GENERATOR};
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

// Montgomery ladder helper
// similar to add-and-double scalar_mult() from elliptic_helpers.rs
// Wikipedie
// R0 ← 0
// R1 ← P
// for i from m downto 0 do
//      if di = 0 then
//          R1 ← point_add(R0, R1)
//          R0 ← point_double(R0)
//      else
//          R0 ← point_add(R0, R1)
//          R1 ← point_double(R1)
// return R0
// We make the assumption that zero will never be placed into N then add a col Q+N without knowing if it is right

// pub fn scalar_mult(trace: &mut TraceTable, point: (FieldElement, FieldElement), scalar: &U256, start: usize, offset: usize, neg: bool)  {
pub fn montgomery_scalar_mult(trace: &mut TraceTable, point: (FieldElement, FieldElement), scalar: &U256, start: usize, offset: usize)  {
    // Add an extra copy of the point then set q to it's negative.
    let mut n = point.clone();
    let mut q: (FieldElement, FieldElement) = (field_element!("00"), field_element!("00"));// point at infinity
    for i in 0..256 {
        trace[(start+i, offset + 1)] = n.0.clone();
        trace[(start+i, offset + 2)] = n.1.clone();
        trace[(start+i, offset + 3)] = q.0.clone();
        trace[(start+i, offset + 4)] = q.1.clone();



        // here we need to go from MSB instead of LSB as in scalar_mult using the add_and_double alg
        if scalar.bit(255 - i) {
            trace[(start + i, offset)] = FieldElement::one();
            n = add(&n.0, &n.1, &q.0, &q.1);
            q = double(&q.0, &q.1);
        } else {
            trace[(start + i, offset)] = FieldElement::zero();
            q = add(&n.0, &n.1, &q.0, &q.1);
            n = double(&n.0, &n.1);
        }

        info!("Trace {:?}, 0: {:?}", i, trace[(i, 0)]);
        info!("Trace {:?}, 1: {:?}", i, trace[(i, 1)]);
        info!("Trace {:?}, 2: {:?}", i, trace[(i, 2)]);
        info!("Trace {:?}, 3: {:?}", i, trace[(i, 3)]);
        info!("Trace {:?}, 4: {:?}", i, trace[(i, 4)]);
        info!("");

    }
}

// Original from elliptic_helpers.rs
// Note attempt to implement for zero too
pub fn double(point_x: &FieldElement, point_y: &FieldElement) -> (FieldElement, FieldElement) {
    //assert!(!(point_x == &FieldElement::ZERO && point_y == &FieldElement::ZERO ));
    if point_x.is_zero() && point_y.is_zero() {
        (field_element!("00"), field_element!("00"))
    }
    else {
        let lambda = ((point_x + point_x + point_x) * point_x + FieldElement::one()) / (point_y + point_y);
        let new_x = (&lambda).square() - point_x - point_x;
        let new_y = lambda * (point_x - &new_x) - point_y;
        (new_x, new_y)
    }
}

// Note attempt to implement for zero too
pub fn add(x_p: &FieldElement, y_p: &FieldElement, x_q: &FieldElement, y_q: &FieldElement) -> (FieldElement, FieldElement) {
    // assert!(!(x_p == &FieldElement::ZERO && y_p == &FieldElement::ZERO));
    // assert!(!(x_q == &FieldElement::ZERO && y_q == &FieldElement::ZERO));
    if x_p.is_zero() && y_p.is_zero() {
        (x_q.clone(), y_q.clone())
    }
    else if x_q.is_zero() && y_q.is_zero(){
        (x_p.clone(), y_p.clone())
    }
    else {
        let lambda = (y_q - y_p) / (x_q - x_p);
        let new_x = (&lambda).square() - (x_p + x_q);
        let new_y = lambda * (x_p - &new_x) - y_p;
        (new_x, new_y)
    }
}

//#[derive(Clone, Debug)]
struct MontgomeryWitness {
    scalar: U256,
    //Note: scalar.bit(i) = i-th LSB, in Montgomery alg., we work from 255th bit to 0th bit
}

//#[derive(Clone, Debug)]
struct MontgomeryClaim {
    x_start : FieldElement,
    y_start : FieldElement,
    x_result : FieldElement,
    y_result : FieldElement,
}

impl Provable<MontgomeryWitness> for MontgomeryClaim {
    #[cfg(feature = "prover")]
    fn trace(&self, witness : MontgomeryWitness) -> TraceTable {
        let mut trace = TraceTable::new(256, 5);
        let start_point = (self.x_start.clone(), self.y_start.clone());

        montgomery_scalar_mult(&mut trace, start_point, &witness.scalar, 0, 0);
        trace
    }
}

impl Verifiable for MontgomeryClaim {
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;
        use zkp_primefield::Pow;

        let trace_length = 256;
        let trace_generator = FieldElement::root(trace_length).unwrap();

        let mut seed = self.x_start.as_montgomery().to_bytes_be().to_vec();
        seed.extend_from_slice(&self.y_start.as_montgomery().to_bytes_be());
        seed.extend_from_slice(&self.x_result.as_montgomery().to_bytes_be());
        seed.extend_from_slice(&self.y_result.as_montgomery().to_bytes_be());

        // Constraint repetitions
        let g = Constant(trace_generator.clone());
        let on_row = |index| (X - g.pow(index)).inv();
        let on_hash_loop_rows = |a: RationalExpression| {
            a * (X.pow(256) - Constant(trace_generator.pow(256 * (trace_length - 1))))
                / (X.pow(trace_length) - FieldElement::one())
        };

        let row_double_R0 = point_double(Trace(1, 0), Trace(2, 0), Trace(1, 1), Trace(2, 1));
        let row_add_R1 = point_add(
            Trace(1, 0),
            Trace(2, 0),
            Trace(3, 0),
            Trace(4, 0),
            Trace(3, 1),
            Trace(4, 1),
        );
        let row_double_R1 = point_double(Trace(3, 0), Trace(4, 0), Trace(3, 1), Trace(4, 1));
        let row_add_R0 = point_add(
            Trace(1, 0),
            Trace(2, 0),
            Trace(3, 0),
            Trace(4, 0),
            Trace(1, 1),
            Trace(2, 1),
        );
        Constraints::from_expressions((trace_length, 5), seed, vec![
            on_hash_loop_rows(simple_conditional(
                row_add_R0[0].clone(),
                Trace(1, 1) - Trace(1, 0),
                Trace(0, 0),
            )),
            on_hash_loop_rows(simple_conditional(
                row_add_R0[1].clone(),
                Trace(2, 1) - Trace(2, 0),
                Trace(0, 0),
            )),
            on_hash_loop_rows(simple_conditional(
                row_double_R1[0].clone(),
                Trace(3, 1) - Trace(3, 0),
                Trace(0, 0),
            )),
            on_hash_loop_rows(simple_conditional(
                row_double_R1[1].clone(),
                Trace(4, 1) - Trace(4, 0),
                Trace(0, 0),
            )),
            on_hash_loop_rows(simple_conditional(
                row_add_R1[0].clone(),
                Trace(3, 1) - Trace(3, 0),
                Constant(1.into()) - Trace(0, 0),
            )),
            on_hash_loop_rows(simple_conditional(
                row_add_R1[1].clone(),
                Trace(4, 1) - Trace(4, 0),
                Constant(1.into()) - Trace(0, 0),
            )),
            on_hash_loop_rows(simple_conditional(
                row_double_R0[0].clone(),
                Trace(1, 1) - Trace(1, 0),
                Constant(1.into()) - Trace(0, 0),
            )),
            on_hash_loop_rows(simple_conditional(
                row_double_R0[1].clone(),
                Trace(2, 1) - Trace(2, 0),
                Constant(1.into()) - Trace(0, 0),
            )),
            // Boundary Constraints
            (Trace(1, 0) - Constant(self.x_start.clone()))*on_row(0),
            (Trace(2, 0) - Constant(self.y_start.clone()))*on_row(0),
            (Trace(1, 0) - Constant(self.x_result.clone()))*on_row(255),
            (Trace(2, 0) - Constant(self.x_result.clone()))*on_row(255),
        ]).unwrap()
    }
}

// Function for creating constraint of point doubling
// from elliptic_helpers.rs
pub fn point_double(input_x: RationalExpression, input_y: RationalExpression, output_x: RationalExpression, output_y: RationalExpression) -> [RationalExpression; 2] {
    use RationalExpression::*;
    let two = Constant(2.into());
    let three = Constant(3.into());

    // These constraints take the lambda = (3x_old^2 + a)/ 2(y_old) and multiply through to clear divisions.
    // This is a multiplied through form of x_new = lambda^2 - 2x_old, which is asserted to be output_x
    let lambda_numb : RationalExpression = three*Exp(input_x.clone().into(), 2) + Constant(1.into());
    let lambda_denom : RationalExpression = two.clone()*input_y.clone();
    let new_x = Exp(lambda_numb.clone().into(), 2) - Exp(lambda_denom.clone().into(), 2)*(two*input_x.clone()+output_x.clone());
    // This is a multipled through form of y_new = lambda*(x_old - x_new) - y_old, which is asserted to be output y.
    let new_y = lambda_numb*(input_x - output_x.clone()) - lambda_denom.clone()*(input_y.clone() + output_y);
    [new_x, new_y]
}

// Function for creating constraints for point addition
// from elliptic_hepers.rs
pub fn point_add(x_p: RationalExpression, y_p: RationalExpression, x_q: RationalExpression, y_q: RationalExpression, x_out: RationalExpression, y_out: RationalExpression) -> [RationalExpression; 2] {
    // These constraints take the lambda = (y_q - y_p)/ (x_q - x_p) and multiply through to clear divisions.
    use RationalExpression::*;
    let lambda_numerator = y_q.clone() - y_p.clone();
    let lambda_denominator = x_q.clone() - x_p.clone();
    let new_x = Exp(lambda_numerator.clone().into(), 2) - Exp(lambda_denominator.clone().into(), 2)*(x_p.clone() + x_q.clone() + x_out.clone());
    let new_y = lambda_numerator*(x_p - x_out) - lambda_denominator*(y_p + y_out);
    [new_x, new_y]
}

// Non secured conditional check, note each input should be it's own valid constraint [ie zero when right]
// from elliptic_helpers.rs[
pub fn simple_conditional(a: RationalExpression, b: RationalExpression, test: RationalExpression) -> RationalExpression {
    use RationalExpression::*;
    a*test.clone() + (Constant(FieldElement::one()) - test.clone())*b
}

fn main() {
    env_logger::init();
    //n_doubling_construction();
    // point_on_curve_construction();
    println!("Start computing of Montgomery ladder trace");
    //montgomery_scalar_mult(trace: &mut TraceTable, point: (FieldElement, FieldElement), scalar: &U256, start: usize, offset: usize)
    let mut trace = TraceTable::new(256, 5);
    let p = (
        field_element!("01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca"),
        field_element!("005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f"),
    );
    let c = u256h!("07374b7d69dc9825fc758b28913c8d2a27be5e7c32412f612b20c9c97afbe4dd");
    montgomery_scalar_mult(&mut trace,  p, &c, 0, 0);

    println!("Finished computing of Montgomery ladder trace");

    println!("Number of set bits on the scalar: {}", c.count_ones());
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