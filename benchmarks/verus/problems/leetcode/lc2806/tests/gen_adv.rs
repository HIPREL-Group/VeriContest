use vstd::prelude::*;

verus! {

pub fn generate_test_case(purchase_amount: i32) -> (result: i32)
    requires
        0 <= purchase_amount <= 100,
    ensures
        0 <= result <= 100,
        result == purchase_amount,
{
    purchase_amount
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_value(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 100,
        2 => 5,
        3 => 4,
        4 => 10,
        5 => 15,
        6 => 25,
        7 => 95,
        8 => 99,
        9 => rng.gen_range_i32(0, 100),
        10 => {
            // multiples of 10
            let k = rng.gen_range_i32(0, 10);
            k * 10
        }
        11 => {
            // values ending in 5
            let k = rng.gen_range_i32(0, 9);
            k * 10 + 5
        }
        12 => {
            // values ending in 4
            let k = rng.gen_range_i32(0, 9);
            k * 10 + 4
        }
        13 => (t % 101) as i32,
        _ => rng.gen_range_i32(0, 100),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 14usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let v = pick_value(&mut rng, mode, t);
        let v = if v < 0 { 0 } else if v > 100 { 100 } else { v };
        let result = generate_test_case(v);
        println!("{{\"purchase_amount\":{}}}", result);
    }
}