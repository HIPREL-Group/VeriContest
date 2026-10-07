use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        0 <= n <= i32::MAX,
    ensures
        0 <= result <= i32::MAX,
{
    n
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
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
    let max = i32::MAX;
    match mode {
        0 => 0,
        1 => rng.gen_range_i32(0, 9),
        2 => rng.gen_range_i32(10, 99),
        3 => rng.gen_range_i32(100, 9999),
        4 => rng.gen_range_i32(10_000, 1_000_000),
        5 => rng.gen_range_i32(1_000_000, max),
        6 => max,
        7 => {
            // powers of 10 minus 1 (all nines)
            let choices = [9, 99, 999, 9999, 99999, 999999, 9999999, 99999999, 999999999];
            choices[rng.next_u64() as usize % choices.len()]
        }
        8 => {
            // multiples of 9
            let k = rng.gen_range_i32(1, 200_000_000);
            k.saturating_mul(9)
        }
        9 => {
            // powers of 2
            let k = rng.gen_range_i32(0, 30) as u32;
            1i32.checked_shl(k).unwrap_or(max)
        }
        _ => rng.gen_range_i32(0, max),
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
        let mut n = pick_for_mode(&mut rng, mode);
        if n < 0 {
            n = 0;
        }
        let out = generate_test_case(n);
        println!("{{\"n\":{}}}", out);
    }
}