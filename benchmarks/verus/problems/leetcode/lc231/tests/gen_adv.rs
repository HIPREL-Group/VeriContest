use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        -2_147_483_648 <= n <= 2_147_483_647,
    ensures
        -2_147_483_648 <= result <= 2_147_483_647,
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, idx: usize) -> i32 {
    match mode {
        0 => {
            // Powers of two (positive)
            let exp = (idx % 31) as u32;
            1i32 << exp
        }
        1 => {
            // Power of two + 1
            let exp = ((idx % 30) + 1) as u32;
            (1i32 << exp) + 1
        }
        2 => {
            // Power of two - 1
            let exp = ((idx % 30) + 1) as u32;
            (1i32 << exp) - 1
        }
        3 => {
            // Negative powers of two
            let exp = (idx % 31) as u32;
            -(1i32 << exp)
        }
        4 => {
            // Zero and small
            (idx as i32) % 5
        }
        5 => {
            // Negative numbers
            rng.gen_range_i32(-2_147_483_648, -1)
        }
        6 => {
            // Extremes
            match idx % 6 {
                0 => i32::MIN,
                1 => i32::MAX,
                2 => 0,
                3 => 1,
                4 => -1,
                _ => 2,
            }
        }
        7 => {
            // Random small
            rng.gen_range_i32(-1000, 1000)
        }
        8 => {
            // Random full range
            rng.gen_range_i32(i32::MIN, i32::MAX)
        }
        9 => {
            // Multiples of 3 (odd non-powers)
            3 * (idx as i32 + 1)
        }
        _ => {
            // Random positive
            rng.gen_range_i32(1, 1_000_000)
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
        let n = pick_for_mode(&mut rng, mode, t);
        let result = generate_test_case(n);
        println!("{{\"n\":{}}}", result);
    }
}