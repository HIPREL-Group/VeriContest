use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n < i32::MAX,
    ensures
        1 <= result < i32::MAX,
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

fn alternating_of_length(k: u32, start_one: bool) -> i32 {
    // Build binary number with k alternating bits, MSB is start_one ? 1 : 0 (but leading 0 just shifts)
    let mut v: i64 = 0;
    let mut bit = if start_one { 1u32 } else { 0u32 };
    for _ in 0..k {
        v = (v << 1) | (bit as i64);
        bit ^= 1;
    }
    if v > (i32::MAX as i64) {
        v = i32::MAX as i64;
    }
    if v < 1 {
        v = 1;
    }
    v as i32
}

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => {
            // Small values
            rng.gen_range_i32(1, 20)
        }
        1 => {
            // Powers of 2 (not alternating except 1 & 2)
            let p = (t % 30) as u32;
            let v = 1i64 << p;
            if v >= i32::MAX as i64 { i32::MAX - 1 } else { v as i32 }
        }
        2 => {
            // Alternating starting with 1: 1, 101, 10101, ...
            let k = ((t % 15) + 1) as u32;
            alternating_of_length(2 * k - 1, true)
        }
        3 => {
            // Alternating starting with 1 with even length: 10, 1010, 101010, ...
            let k = ((t % 15) + 1) as u32;
            alternating_of_length(2 * k, true)
        }
        4 => {
            // All ones: 2^k - 1
            let k = ((t % 30) + 1) as u32;
            let v = (1i64 << k) - 1;
            if v >= i32::MAX as i64 { i32::MAX - 1 } else if v < 1 { 1 } else { v as i32 }
        }
        5 => {
            // Large near MAX
            rng.gen_range_i32(i32::MAX - 1000, i32::MAX - 1)
        }
        6 => {
            // Random full range
            rng.gen_range_i32(1, i32::MAX - 1)
        }
        7 => {
            // 2^k + 1
            let k = ((t % 28) + 2) as u32;
            let v = (1i64 << k) + 1;
            if v >= i32::MAX as i64 { i32::MAX - 1 } else { v as i32 }
        }
        8 => {
            // 2^k - 2 (ends in 0)
            let k = ((t % 28) + 2) as u32;
            let v = (1i64 << k) - 2;
            if v < 1 { 1 } else if v >= i32::MAX as i64 { i32::MAX - 1 } else { v as i32 }
        }
        9 => {
            // Specific edge cases
            let cases = [1i32, 2, 3, 4, 5, 6, 7, 10, 11, 21, 42, 85, 170, 341, 682, 1365, 2730, 5461];
            cases[t % cases.len()]
        }
        _ => {
            rng.gen_range_i32(1, 1000)
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
        let mut n = pick_for_mode(&mut rng, mode, t);
        if n < 1 { n = 1; }
        if n >= i32::MAX { n = i32::MAX - 1; }
        let result = generate_test_case(n);
        println!("{{\"n\":{}}}", result);
    }
}