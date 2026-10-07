use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i32) -> (res: i32)
    requires
        1 <= num,
        num <= i32::MAX,
    ensures
        1 <= res <= i32::MAX,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    let max_val: i32 = i32::MAX; // 2^31 - 1
    match mode {
        0 => 1,
        1 => 2,
        2 => 5,
        3 => max_val, // 2^31 - 1, all bits set
        4 => {
            // Power of 2
            let k = (rng.next_u64() % 31) as u32;
            1i32 << k
        }
        5 => {
            // Power of 2 minus 1
            let k = 1 + (rng.next_u64() % 31) as u32;
            if k == 31 {
                max_val
            } else {
                (1i32 << k) - 1
            }
        }
        6 => {
            // Power of 2 plus 1
            let k = 1 + (rng.next_u64() % 30) as u32;
            (1i32 << k) + 1
        }
        7 => {
            // Small numbers
            rng.gen_range_i32(1, 20)
        }
        8 => {
            // Medium numbers
            rng.gen_range_i32(1, 1_000_000)
        }
        9 => {
            // Large numbers near max
            rng.gen_range_i32(max_val - 1000, max_val)
        }
        _ => {
            // Full range random
            rng.gen_range_i32(1, max_val)
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
        let out = generate_test_case(num);
        println!("{{\"num\":{}}}", out);
    }
}