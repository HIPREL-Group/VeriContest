use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64) -> (res: i64)
    requires
        1 <= n <= 1_000_000_000,
    ensures
        1 <= res <= 1_000_000_000,
{
    n
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn pick_n(rng: &mut Rng, mode: usize) -> i64 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 4,
        4 => 5,
        5 => 1_000_000_000,
        6 => 999_999_999,
        7 => 999_999_998,
        8 => {
            // multiples of 3
            let k = rng.gen_range_i64(1, 333_333_333);
            3 * k
        }
        9 => {
            // 3k+1
            let k = rng.gen_range_i64(0, 333_333_332);
            3 * k + 1
        }
        10 => {
            // 3k+2
            let k = rng.gen_range_i64(0, 333_333_332);
            3 * k + 2
        }
        11 => {
            // small
            rng.gen_range_i64(1, 100)
        }
        12 => {
            // near max
            rng.gen_range_i64(999_000_000, 1_000_000_000)
        }
        _ => rng.gen_range_i64(1, 1_000_000_000),
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
        let n_raw = pick_n(&mut rng, mode);
        let n = if n_raw < 1 { 1 } else if n_raw > 1_000_000_000 { 1_000_000_000 } else { n_raw };
        let out = generate_test_case(n);
        println!("{{\"n\":{}}}", out);
    }
}