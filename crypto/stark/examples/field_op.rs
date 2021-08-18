#![warn(clippy::all)]
use env_logger;
use log::info;
use std::time::Instant;
use zkp_macros_decl::field_element;
use zkp_primefield::{FieldElement, Root, One};
use zkp_stark::{Constraints, Provable, RationalExpression, TraceTable, Verifiable};
use zkp_u256::U256;

#[derive(Clone, Debug)]
struct ComputeMClaim {
    x: FieldElement,
    y: FieldElement,
    value: FieldElement,
}

impl Verifiable for ComputeMClaim{
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;
        let trace_generator = FieldElement::root(4).unwrap();
        let g = Constant(trace_generator);

        let m_trace : RationalExpression =  ((Trace(0,0) + Trace(0,0) + Trace(0,0)) * Trace(0,0) + Constant(FieldElement::one()) ) / ( Trace(0, 1) + Trace(0, 1));

        Constraints::from_expressions((8, 1), self.value.as_montgomery().to_bytes_be().to_vec(), vec![
            (Trace(0, 0) - Constant(self.x.clone())) / (X - 1),
            (Trace(0, 1) - Constant(self.y.clone())) / (X - 1),
            (Trace(0, 2) - Constant(self.value.clone())) / (X - 1),
            (Trace(0, 3) -
                ((Trace(0,0) + Trace(0,0) + Trace(0,0)) * Trace(0,0)
                    + Constant(FieldElement::one()))) / (X - 1),
            (Trace(0, 4) - ( Trace(0, 1) + Trace(0, 1))) / (X - 1),
            (Trace(0,2) * Trace(0, 4) - Trace(0, 3)) / (X - 1),
        ])
            .unwrap()
    }
}

impl Provable<&Witness> for ComputeMClaim{
    fn trace(&self, witness: &Witness) -> TraceTable {
        let mut trace = TraceTable::new(8, 1);
        trace[(0, 0)] = self.x.clone();
        trace[(1, 0)] = self.y.clone();
        trace[(2, 0)] = self.value.clone();
        trace[(3, 0)] = (trace[(0,0)].clone() + trace[(0,0)].clone() + trace[(0,0)].clone()) * trace[(0,0)].clone()
            + FieldElement::one();
        trace[(4, 0)] = trace[(1, 0)].clone() + trace[(1, 0)].clone();
        println!("[0, 0] = {:?}",trace[(0, 0)] );
        println!("[1, 0] = {:?}",trace[(1, 0)] );
        println!("[2, 0] = {:?}",trace[(2, 0)] );
        println!("[3, 0] = {:?}",trace[(3, 0)] );
        println!("[4, 0] = {:?}",trace[(4, 0)] );
        trace
    }
}

#[derive(Clone, Debug)]
struct InversionClaim {
    value: FieldElement,
}

impl Verifiable for InversionClaim{
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;
        let trace_generator = FieldElement::root(2).unwrap();
        let g = Constant(trace_generator);
        Constraints::from_expressions((2, 1), self.value.as_montgomery().to_bytes_be().to_vec(), vec![
            (Trace(0, 0) * Trace(0, 1) -1) / (X - 1),
            // (Trace(0, 1) - Constant(self.value.clone())) / (X - 1), taky funguje
            (Trace(0, 0) - Constant(self.value.clone())) / (X - g),
        ])
            .unwrap()
    }
}

impl Provable<&Witness> for InversionClaim{
    fn trace(&self, witness: &Witness) -> TraceTable {
        let mut trace = TraceTable::new(2, 1);
        trace[(0, 0)] = witness.secret.clone();
        trace[(1, 0)] = self.value.clone();
        println!("[0,0] = {:?}",trace[(0, 0)] );
        println!("[1,0] = {:?}",trace[(1, 0)] );
        let check = trace[(0,0)].clone() * trace[(1, 0)].clone();
        println!("check = {:?}",check);
        trace
    }
}


#[derive(Clone, Debug)]
struct Witness {
    secret: FieldElement,
}

#[derive(Clone, Debug)]
struct AddNTimesClaim {
    index: usize,
    value: FieldElement,
}
impl Verifiable for AddNTimesClaim {
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
            (Trace(1, 1) - Trace(1, 0)) * every_row(),
            (Trace(0, 1) - Trace(0, 0) - Trace(1, 0)) * every_row(),
            (Trace(0, 0) - 0) * on_row(0),
            (Trace(0, 0) - &self.value) * on_row(self.index),
        ])
            .unwrap()
    }
}
impl Provable<&Witness> for AddNTimesClaim {
    fn trace(&self, witness: &Witness) -> TraceTable {
        let trace_length = self.index.next_power_of_two();
        let mut trace = TraceTable::new(trace_length, 2);
        trace[(0, 0)] = self.value.clone();
        trace[(0, 1)] = witness.secret.clone();
        for i in 0..(trace_length - 1) {
            trace[(i + 1, 1)] = witness.secret.clone();
            trace[(i + 1, 0)] = &trace[(i, 0)] + &trace[(i, 1)];
            // trace[(i + 1, 1)] = trace[(i, 1)].clone();
            // trace[(i + 1, 0)] = &trace[(i, 0)] + &trace[(i, 1)];
        }
        trace
    }
}
fn main() {
    // FindingMatchAdd();
    //AddNTimesConstruction()
    // InversionConstruction();
    ComputeMConstruction();
}

fn ComputeMConstruction(){
    env_logger::init();
    info!("Constructing claim");
    let claim = ComputeMClaim {
        x : field_element!("01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca") ,
        y : field_element!("005668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f"),
        value: field_element!("03a2fcd28a5ba01b5ed8a1c16da45138f4df4fb7b845bbfcea5295bbfad92610"),
    };
    let mut constraints = claim.constraints();
    constraints.num_queries = 2;
    constraints.pow_bits = 10;

    info!("Claim: {:?}", claim);

    info!("Constructing witness");
    let witness = Witness {
        secret : field_element!("00"),
    };

    info!("Witness: {:?}", witness);
    let trace = claim.trace(&witness);
    assert_eq!(claim.check(&witness), Ok(()));

    // Start timer
    let start = Instant::now();

    info!("Constructing proof...");
    let _proof = claim.prove(&witness).unwrap();

    // Measure time
    let duration = start.elapsed();
    info!("Time elapsed in proof function is: {:?}", duration);
}

fn InversionConstruction(){
    env_logger::init();
    info!("Constructing claim");
    let claim = InversionClaim {
        // value : field_element!("01"),
        // value : field_element!("02"),
        value : field_element!("03"),
        // value : field_element!("04"),
        // value : field_element!("05"),
        // value : field_element!("06"),
        // value : field_element!("07"),
        // value : field_element!("08"),
        // value : field_element!("09"),
        // value : field_element!("10"),
    };
    let mut constraints = claim.constraints();
    constraints.num_queries = 2;
    constraints.pow_bits = 10;

    info!("Claim: {:?}", claim);

    info!("Constructing witness");
    let witness = Witness {
        // secret: field_element!("01")
        // secret: field_element!("0400000000000008800000000000000000000000000000000000000000000001"),
        secret: field_element!("02aaaaaaaaaaaab0555555555555555555555555555555555555555555555556"),
        // secret: field_element!("060000000000000cc00000000000000000000000000000000000000000000001"),
        // secret: field_element!("0666666666666674000000000000000000000000000000000000000000000001"),
        // secret: field_element("01555555555555582aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab")
        // secret: field_element("06db6db6db6db6ea000000000000000000000000000000000000000000000001")
        // secret: field_element("070000000000000ee00000000000000000000000000000000000000000000001")
        // secret: field_element("0638e38e38e38e461c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c8")
        // secret: field_element("0733333333333342800000000000000000000000000000000000000000000001")
    };
    info!("Witness: {:?}", witness);
    let trace = claim.trace(&witness);
    assert_eq!(claim.check(&witness), Ok(()));

    // Start timer
    let start = Instant::now();

    info!("Constructing proof...");
    let _proof = claim.prove(&witness).unwrap();

    // Measure time
    let duration = start.elapsed();
    info!("Time elapsed in proof function is: {:?}", duration);

}
//TODO parameters for index, value and secret
fn AddNTimesConstruction(){
    env_logger::init();

    info!("Constructing claim");
    let claim = AddNTimesClaim {
        // index: 1000,
        // value: field_element!("0142c45e5d743d10eae7ebb70f1526c65de7dbcdb65b322b6ddc36a812591e8f"),
        index : 5,
        value: field_element!("0f")
    };
    info!("Claim: {:?}", claim);

    info!("Constructing witness");
    let witness = Witness {
        // secret: field_element!("cafebabe"),
        secret: field_element!("03"),
    };
    info!("Witness: {:?}", witness);
    // assert_eq!(claim.check(&witness), Ok(()));

    // Start timer
    let start = Instant::now();

    info!("Constructing proof...");
    let _proof = claim.prove(&witness).unwrap();

    // Measure time
    let duration = start.elapsed();
    info!("Time elapsed in proof function is: {:?}", duration);
}

fn FindingMatchAdd(){
    env_logger::init();

    info!("Constructing witness");
    let witness = Witness {
        // secret: field_element!("cafebabe"),
        secret: field_element!("03"),
    };
    info!("Witness: {:?}", witness);

    let mut cx = FieldElement::one();
    for n in 1..1001 {
        let claim2 = AddNTimesClaim {
            index: 5,
            value: cx.clone(),  // or: FieldElement::from_uint(&U256::from(n))
        };
        // println!("Checking for secret {:?} and value {:?}", witness.secret, cx);
        if claim2.check(&witness) == Ok(()) {
            println!("Found the match {:?}, {:?}", n, cx);
            break;
        }
        cx += FieldElement::one();
    }
}