use vstd::prelude::*;

verus! {

pub fn generate_test_case(p: i32) -> (result: i32)
    requires
        1 <= p <= 60,
    ensures
        1 <= result <= 60,
{
    p
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn print_json(p: i32) {
    println!("{{\"p\":{}}}", p);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);

    // Adversarial: boundary p values
    let boundary: Vec<i32> = vec![1, 2, 3, 4, 5, 6, 7, 8, 15, 16, 30, 31, 32, 59, 60];
    for &p in boundary.iter() {
        let q = generate_test_case(p);
        print_json(q);
    }

    // Mode-based generation
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let p: i32 = match mode {
            0 => 1,
            1 => 60,
            2 => rng.gen_range_i32(1, 5),
            3 => rng.gen_range_i32(55, 60),
            4 => rng.gen_range_i32(28, 33),
            5 => rng.gen_range_i32(1, 60),
            6 => {
                let small = [1, 2, 3];
                small[(rng.next_u64() as usize) % small.len()]
            }
            7 => {
                let big = [58, 59, 60];
                big[(rng.next_u64() as usize) % big.len()]
            }
            8 => rng.gen_range_i32(10, 20),
            _ => rng.gen_range_i32(40, 55),
        };
        let q = generate_test_case(p);
        print_json(q);
    }
}