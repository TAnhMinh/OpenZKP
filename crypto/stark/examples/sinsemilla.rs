use zkp_macros_decl::field_element;
use zkp_macros_decl::u256h;
use zkp_u256::U256;
use zkp_primefield::{FieldElement, One, SquareInline, Zero, Root};
use zkp_stark::RationalExpression::*;
use zkp_stark::{Constraints, Provable, RationalExpression, TraceTable, Verifiable};
use zkp_primefield::u256::Binary;
use zkp_elliptic_curve::{ScalarFieldElement, Affine, window_table_affine};
use env_logger;
use log::info;
use crate::ecc_edited_helpers::*;
use std::time::Instant;

mod ecc_edited_helpers;

// Q from
// generated as E.gens() in sage
pub const Q: (FieldElement, FieldElement) = (
    field_element!("006a5158f04306cef4b1f5aaf8f1f526df12610ef9c887a15b3ce889026713a0"),
    field_element!("0712cc1ae399832de8d77288bb9fb18ac0d0eb518926caf8c621204ba21bf450")
);

// P from
// generated as E.random_element()
pub const P: (FieldElement, FieldElement) = (
    field_element!("0684e355013c3279284f196c2f7482464f90b1d8148a848374fb0f4f9252097d"),
    field_element!("0670608843e71391085ffe01a161e5a36129de68dd8b26a8e446feb0ad025bbe")
);

// Witness for scalar_mul claim
#[derive(Clone, Debug)]
struct Witness {
    scalar: U256,
}

// Scalar_mult claim
#[derive(Clone, Debug)]
struct Claim {
    x_start : FieldElement,
    y_start : FieldElement,
    x_result : FieldElement,
    y_result : FieldElement,
}

// for scalar multiplication
impl Provable<&Witness> for Claim {
    #[cfg(feature = "prover")]
    fn trace(&self, witness : &Witness) -> TraceTable {
        let mut trace = TraceTable::new(256, 5);
        let start_point = (self.x_start.clone(), self.y_start.clone());
        scalar_mult(&mut trace, start_point, &witness.scalar, 0, 0, false);
        trace
    }
}

// for scalar multiplication
impl Verifiable for Claim {
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

        let row_double = point_double(Trace(1, 0), Trace(2, 0), Trace(1, 1), Trace(2, 1));
        let row_add = point_add(
            Trace(1, 0),
            Trace(2, 0),
            Trace(3, 0),
            Trace(4, 0),
            Trace(3, 1),
            Trace(4, 1),
        );

        Constraints::from_expressions((trace_length, 5), seed, vec![
            on_hash_loop_rows(row_double[0].clone()),
            on_hash_loop_rows(row_double[1].clone()),
            on_hash_loop_rows(one_or_zero((Trace(0,0) - Constant(2.into())*Trace(0, 1)))),
            on_hash_loop_rows(simple_conditional(
                row_add[0].clone(),
                Trace(3, 1) - Trace(3, 0),
                Trace(0,0) - Constant(2.into())*Trace(0, 1))),
            on_hash_loop_rows(simple_conditional(
                row_add[1].clone(),
                Trace(4, 1) - Trace(4, 0),
                Trace(0,0) - Constant(2.into())*Trace(0, 1))),
            // Boundary Constraints
            // the following two lines correct when in scalar_mult we in fact accept max 255 bit scalars
            (Trace(1, 0) - Constant(self.x_start.clone()))*on_row(0),
            (Trace(2, 0) - Constant(self.y_start.clone()))*on_row(0),
            (Trace(3, 0) - Constant(self.x_result.clone()))*on_row(255),
            (Trace(4, 0) - Constant(self.y_result.clone()))*on_row(255),

        ]).unwrap()
    }
}

// Witness for sinsemilla claim, message of 2 blocks of 256 bits
#[derive(Clone, Debug)]
struct SinsemillaWitness {
    m1: U256,
    m2: U256
}

// Scalar_mult claim
#[derive(Clone, Debug)]
struct SinsemillaClaim {
    x_result : FieldElement,
    y_result : FieldElement,
    blocks_num: usize,
}

// for Sinsemilla Claim
impl Provable<&SinsemillaWitness> for SinsemillaClaim {
    #[cfg(feature = "prover")]
    fn trace(&self, witness : &SinsemillaWitness) -> TraceTable {
        let mut trace = TraceTable::new(512, 11);
        let start_point = (P.0, P.1);
        trace[(0, 0)] = Q.0;
        trace[(0, 1)] = Q.1;
        scalar_mult(&mut trace, start_point.clone(), &witness.m1, 0, 2, false);

        // Acc_i+1 = Acc_i + m_i*P + Acc_i, i = 0
        let acc_1_aux = add(&Q.0, &Q.1, &trace[(255, 5)], &trace[(255, 6)]);
        trace[(255, 7)] = acc_1_aux.0;
        trace[(255, 8)] = acc_1_aux.1;
        let acc_1_fin = add(&Q.0, &Q.1, &trace[(255, 7)], &trace[(255, 8)]);
        trace[(255, 9)] = acc_1_fin.0;
        trace[(255, 10)] = acc_1_fin.1;

        trace[(0, 0)] = trace[(255, 9)].clone();
        trace[(0, 1)] = trace[(255, 10)].clone();
        scalar_mult(&mut trace, start_point.clone(), &witness.m2, 256, 2, true);

        // Acc_i+1 = Acc_i + m_i*P + Acc_i, i = 1
        let acc_2_aux = add(&Q.0, &Q.1, &trace[(511, 5)], &trace[(512, 6)]);
        trace[(511, 7)] = acc_2_aux.0;
        trace[(511, 8)] = acc_2_aux.1;
        let acc_2_fin = add(&Q.0, &Q.1, &trace[(511, 7)], &trace[(512, 8)]);
        trace[(511, 9)] = acc_2_fin.0;
        trace[(511, 10)] = acc_2_fin.1;
        trace
    }
}

impl Verifiable for SinsemillaClaim {
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;
        use zkp_primefield::Pow;

        let trace_length = 256;
        let trace_generator = FieldElement::root(trace_length).unwrap();

        let mut seed = self.x_result.as_montgomery().to_bytes_be().to_vec();
        seed.extend_from_slice(&self.y_result.as_montgomery().to_bytes_be());

        // Constraint repetitions
        let g = Constant(trace_generator.clone());
        let on_row = |index| (X - g.pow(index)).inv();
        let on_hash_loop_rows = |a: RationalExpression| {
            a * (X.pow(256) - Constant(trace_generator.pow(256 * (trace_length - 1))))
                / (X.pow(trace_length) - FieldElement::one())
        };

        let row_double = point_double(Trace(1, 0), Trace(2, 0), Trace(1, 1), Trace(2, 1));
        let row_add = point_add(
            Trace(1, 0),
            Trace(2, 0),
            Trace(3, 0),
            Trace(4, 0),
            Trace(3, 1),
            Trace(4, 1),
        );

        Constraints::from_expressions((trace_length, 11), seed, vec![
            on_hash_loop_rows(row_double[0].clone()),
            on_hash_loop_rows(row_double[1].clone()),
            on_hash_loop_rows(one_or_zero((Trace(0,0) - Constant(2.into())*Trace(0, 1)))),
            on_hash_loop_rows(simple_conditional(
                row_add[0].clone(),
                Trace(3, 1) - Trace(3, 0),
                Trace(0,0) - Constant(2.into())*Trace(0, 1))),
            on_hash_loop_rows(simple_conditional(
                row_add[1].clone(),
                Trace(4, 1) - Trace(4, 0),
                Trace(0,0) - Constant(2.into())*Trace(0, 1))),
            // Boundary Constraints
            // the following two lines correct when in scalar_mult we in fact accept max 255 bit scalars
            (Trace(3, 0) - Constant(self.x_result.clone()))*on_row(512),
            (Trace(4, 0) - Constant(self.y_result.clone()))*on_row(512),

        ]).unwrap()
    }
}

fn sinsemilla(message : Vec<U256>)->(FieldElement, FieldElement){
    let mut acc = Affine::Point{ x: Q.0, y: Q.1 };
    let p = Affine::Point {x: P.0, y: P.1};
    let n = message.len();
    for i in 0..n {
        let m_scalar = ScalarFieldElement::from(message[i].clone());
        acc = acc.double() + p.clone() * m_scalar
    }
    // match checked_division(dividend, divisor) {
    //     None => println!("{} / {} failed!", dividend, divisor),
    //     Some(quotient) => {
    //         println!("{} / {} = {}", dividend, divisor, quotient)
    //     },
    // }
    match acc.as_coordinates() {
        None => (FieldElement::zero(), FieldElement::zero()),
        Some((x, y)) => (x.clone(), y.clone())
    }
}

fn main() {
    // How to know the non-montgomery form of shift.x, shift.y
    // println!("shift_x: {:?}", SHIFT_POINT.0);
    // println!("shift_y: {:?}", SHIFT_POINT.1);
    //smult_construction();

    //Test sinsemilla function
    let mut message : Vec<U256> = Vec::new();
    message.push(u256h!("dead"));
    message.push(u256h!("cafe"));
    message.push(u256h!("babe"));

    let res = sinsemilla(message);
    println!("Result x: {:?}", res.0);
    println!("Result y: {:?}", res.1);

}


//scalar_mult BUT with shifting!
fn smult_construction(){
    env_logger::init();

    // From algebra/elliptic-curve/src/curve.rs tests, the expected point computed in Sage
    info!("Constructing claim");
    let claim = Claim {
        x_start: field_element!("01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca"),
        y_start: field_element!("005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f"),
        x_result: field_element!("07e7981dbdcab7a12e82a71563265fe17d1e468def04dc824c342bd113b8a6ba"),
        y_result: field_element!("074af28209b54a0943e10972953ae3acc93ca2d74caf5b07c0a833fbb9aba0ff")
    };
    info!("Claim: {:?}", claim);

    info!("Constructing witness");
    let witness = Witness {
        scalar : u256h!("03"),
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