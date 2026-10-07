use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, limit_val: i32) -> (result: (i32, i32))
    requires
        1 <= n_val <= 50,
        1 <= limit_val <= 50,
    ensures
        1 <= result.0 <= 50,
        1 <= result.1 <= 50,
{
    (n_val, limit_val)
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

fn pick_test_case(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (50, 50),
        2 => (1, 50),
        3 => (50, 1),
        4 => (3, 3),
        5 => (5, 2),
        6 => {
            let limit = rng.gen_range_i32(1, 50);
            let n = rng.gen_range_i32(1, (3 * limit).min(50));
            (n, limit)
        }
        7 => {
            let limit = rng.gen_range_i32(1, 50);
            let n = (3 * limit).min(50);
            (n.max(1), limit)
        }
        8 => {
            let n = rng.gen_range_i32(1, 50);
            let limit = rng.gen_range_i32(1, 3).min(50);
            (n, limit.max(1))
        }
        9 => {
            let n = rng.gen_range_i32(1, 50);
            let limit = 50;
            (n, limit)
        }
        _ => {
            let n = rng.gen_range_i32(1, 50);
            let limit = rng.gen_range_i32(1, 50);
            (n, limit)
        }
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, limit) = pick_test_case(&mut rng, mode);
        let (n_out, limit_out) = generate_test_case(n, limit);
        println!("{{\"n\": {}, \"limit\": {}}}", n_out, limit_out);
    }
}