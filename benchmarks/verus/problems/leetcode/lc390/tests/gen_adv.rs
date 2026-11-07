use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1_000_000_000,
    ensures
        1 <= result <= 1_000_000_000,
        result == n,
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_n(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => {
            // powers of 2
            let k = (t % 30) as u32;
            let v: i64 = 1i64 << k;
            if v > 1_000_000_000 { 1_000_000_000 } else { v as i32 }
        }
        4 => {
            // powers of 2 minus 1
            let k = ((t % 30) + 1) as u32;
            let v: i64 = (1i64 << k) - 1;
            if v > 1_000_000_000 { 1_000_000_000 } else if v < 1 { 1 } else { v as i32 }
        }
        5 => {
            // powers of 2 plus 1
            let k = (t % 30) as u32;
            let v: i64 = (1i64 << k) + 1;
            if v > 1_000_000_000 { 1_000_000_000 } else { v as i32 }
        }
        6 => 1_000_000_000,
        7 => 999_999_999,
        8 => {
            // small values
            rng.gen_range_i32(1, 20)
        }
        9 => {
            // random medium
            rng.gen_range_i32(1, 100_000)
        }
        _ => {
            // random large
            rng.gen_range_i32(1, 1_000_000_000)
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
        let n = pick_n(&mut rng, mode, t);
        let n = if n < 1 { 1 } else if n > 1_000_000_000 { 1_000_000_000 } else { n };
        let result = generate_test_case(n);
        println!("{{\"n\": {}}}", result);
    }
}