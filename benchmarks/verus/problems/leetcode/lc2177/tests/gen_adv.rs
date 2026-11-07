use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i64) -> (result: i64)
    requires
        0 <= num <= 1000000000000000,
    ensures
        0 <= result <= 1000000000000000,
        result == num,
{
    num
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i64 {
    let max_val: i64 = 1_000_000_000_000_000;
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => max_val,
        5 => max_val - 1,
        6 => max_val - 2,
        7 => {
            // multiple of 3
            let k = rng.gen_range_i64(0, max_val / 3);
            k * 3
        }
        8 => {
            // multiple of 3 + 1
            let k = rng.gen_range_i64(0, (max_val - 1) / 3);
            k * 3 + 1
        }
        9 => {
            // multiple of 3 + 2
            let k = rng.gen_range_i64(0, (max_val - 2) / 3);
            k * 3 + 2
        }
        10 => {
            // small values
            rng.gen_range_i64(0, 100)
        }
        11 => {
            // near boundary
            rng.gen_range_i64(max_val - 1000, max_val)
        }
        12 => {
            // powers of 10
            let exps = [1i64, 10, 100, 1000, 10_000, 100_000, 1_000_000, 1_000_000_000, 1_000_000_000_000, 1_000_000_000_000_000];
            let idx = (rng.next_u64() as usize) % exps.len();
            exps[idx]
        }
        _ => rng.gen_range_i64(0, max_val),
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let num = pick_for_mode(&mut rng, mode);
        let validated = generate_test_case(num);
        println!("{{\"num\":{}}}", validated);
    }
}