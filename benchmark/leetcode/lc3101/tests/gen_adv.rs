use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<u8>) -> (nums: Vec<i32>)
    requires
        1 <= bits.len() <= 100000,
        forall |i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i] == 0u8 || #[trigger] bits[i] == 1u8),
    ensures
        1 <= nums.len() <= 100000,
        nums.len() == bits.len(),
        forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0i32 || #[trigger] nums[i] == 1i32),
{
    let n = bits.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k] == 0u8 || #[trigger] bits[k] == 1u8),
            forall |k: int| 0 <= k < i as int ==> (#[trigger] nums[k] == 0i32 || #[trigger] nums[k] == 1i32),
        decreases n - i,
    {
        let b = bits[i];
        if b == 0u8 {
            nums.push(0i32);
        } else {
            nums.push(1i32);
        }
        i = i + 1;
    }
    nums
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bit(&mut self) -> u8 {
        (self.next_u64() & 1) as u8
    }
}

fn build_bits(mode: usize, n: usize, rng: &mut Rng) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        2 => {
            // alternating starting 0
            for i in 0..n { v.push((i % 2) as u8); }
        }
        3 => {
            // alternating starting 1
            for i in 0..n { v.push(((i + 1) % 2) as u8); }
        }
        4 => {
            // random uniform
            for _ in 0..n { v.push(rng.gen_bit()); }
        }
        5 => {
            // blocks of repeated bits
            let mut cur: u8 = 0;
            let mut remaining = n;
            while remaining > 0 {
                let blen = rng.gen_range_usize(1, remaining.min(10));
                for _ in 0..blen { v.push(cur); }
                remaining -= blen;
                cur ^= 1;
            }
        }
        6 => {
            // long alternating run then constant
            let half = n / 2;
            for i in 0..half { v.push((i % 2) as u8); }
            let last = if half > 0 { v[half - 1] } else { 0 };
            for _ in half..n { v.push(last); }
        }
        7 => {
            // one flip at random location, rest alternating
            for i in 0..n { v.push((i % 2) as u8); }
            if n > 0 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] ^= 1;
            }
        }
        8 => {
            // mostly zeros, sparse ones
            for _ in 0..n { v.push(0); }
            let ones = rng.gen_range_usize(0, n.min(5));
            for _ in 0..ones {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = 1;
            }
        }
        9 => {
            // pairs 00 11 00 11
            let mut cur: u8 = 0;
            let mut count = 0;
            for _ in 0..n {
                v.push(cur);
                count += 1;
                if count == 2 { count = 0; cur ^= 1; }
            }
        }
        _ => {
            // biased random
            for _ in 0..n {
                let r = rng.next_u64() % 4;
                v.push(if r == 0 { 1 } else { 0 });
            }
        }
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 20),
            1 => 2 + (t % 50),
            2 => 100000,
            3 => 99999,
            4 => rng.gen_range_usize(1, 500),
            5 => rng.gen_range_usize(10, 1000),
            6 => rng.gen_range_usize(2, 200),
            7 => rng.gen_range_usize(5, 300),
            8 => rng.gen_range_usize(1, 100),
            9 => 2 + (t % 80),
            _ => rng.gen_range_usize(1, 5000),
        };
        let n = if n == 0 { 1 } else if n > 100000 { 100000 } else { n };
        let bits = build_bits(mode, n, &mut rng);
        let nums = generate_test_case(&bits);
        print_json(&nums);
    }
}