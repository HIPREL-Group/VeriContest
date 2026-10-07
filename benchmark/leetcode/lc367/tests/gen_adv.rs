use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i32) -> (result: i32)
    requires
        1 <= num <= i32::MAX,
    ensures
        1 <= result <= i32::MAX,
{
    num
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => i32::MAX,
        2 => {
            // Perfect square: k*k for small k
            let k = rng.gen_range_i32(1, 46340);
            k * k
        }
        3 => {
            // Perfect square near max: 46340^2 = 2147395600
            46340i32 * 46340i32
        }
        4 => {
            // Near-perfect-square: k*k + 1
            let k = rng.gen_range_i32(1, 46340);
            let sq = k * k;
            if sq < i32::MAX { sq + 1 } else { sq }
        }
        5 => {
            // Near-perfect-square: k*k - 1
            let k = rng.gen_range_i32(2, 46340);
            k * k - 1
        }
        6 => {
            // Small numbers
            rng.gen_range_i32(1, 20)
        }
        7 => {
            // Power of 2
            let e = rng.gen_range_i32(0, 30);
            1i32 << e
        }
        8 => {
            // Large random
            rng.gen_range_i32(1_000_000_000, i32::MAX)
        }
        9 => {
            // Medium random
            rng.gen_range_i32(1, 1_000_000)
        }
        _ => {
            rng.gen_range_i32(1, i32::MAX)
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let num = pick_for_mode(&mut rng, mode);
        let num = if num < 1 { 1 } else { num };
        let result = generate_test_case(num);
        println!("{{\"num\":{}}}", result);
    }
}