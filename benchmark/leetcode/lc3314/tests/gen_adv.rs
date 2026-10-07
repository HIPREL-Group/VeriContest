use vstd::prelude::*;

verus! {

pub open spec fn is_prime(n: int) -> bool {
    n >= 2 && forall|d: int| 2 <= d < n ==> #[trigger] (n % d) != 0
}

pub fn prime_input(n: i32) -> (result: bool)
    requires 2 <= n <= 1000,
    ensures result == is_prime(n as int),
{
    let mut d = 2i32;
    while d < n
        invariant
            2 <= d <= n <= 1000,
            forall|k: int| 2 <= k < d ==> #[trigger] (n as int % k) != 0,
        decreases n - d,
    {
        if n % d == 0 { return false; }
        d += 1;
    }
    true
}

pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 2 <= #[trigger] result[i] <= 1000,
        forall|i: int| 0 <= i < result.len() ==> is_prime(#[trigger] result[i] as int),
{
    let n = if raw.len() < 1 { 1usize } else if raw.len() > 100 { 100usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 2 <= #[trigger] result[j] <= 1000,
            forall|j: int| 0 <= j < result.len() ==> is_prime(#[trigger] result[j] as int),
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 2 };
        let v = if v < 2 { 2 } else if v > 1000 { 1000 } else { v };
        let v = if prime_input(v) { v } else { 2 };
        result.push(v);
        i += 1;
    }
    result
}


pub fn generate_candidate(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 100,
        forall|i: int| 0 <= i < vals.len() ==> #[trigger] vals[i] >= 2,
        forall|i: int| 0 <= i < vals.len() ==> #[trigger] vals[i] <= 1000,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 2,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall|k: int| 0 <= k < vals.len() ==> #[trigger] vals[k] >= 2,
            forall|k: int| 0 <= k < vals.len() ==> #[trigger] vals[k] <= 1000,
        decreases n - i,
    {
        nums.push(vals[i]);
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
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

// Primes up to 1000
const PRIMES: &[i32] = &[
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
    421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
    509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607,
    613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
    709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811,
    821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911,
    919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
];

fn pick_prime(rng: &mut Rng) -> i32 {
    let idx = rng.gen_range(0, PRIMES.len() - 1);
    PRIMES[idx]
}

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 100,
        2 => rng.gen_range(1, 10),
        3 => rng.gen_range(50, 100),
        4 => rng.gen_range(1, 100),
        5 => 2,
        6 => rng.gen_range(1, 100),
        7 => rng.gen_range(1, 100),
        8 => rng.gen_range(1, 100),
        9 => rng.gen_range(1, 100),
        _ => rng.gen_range(1, 100),
    };
    let mut v = Vec::with_capacity(n);
    match mode {
        5 => {
            // all 2s
            for _ in 0..n { v.push(2); }
        }
        6 => {
            // all 3s
            for _ in 0..n { v.push(3); }
        }
        7 => {
            // all 997 (large)
            for _ in 0..n { v.push(997); }
        }
        8 => {
            // Mersenne-like primes: 3, 7, 31, 127
            let mers = [3, 7, 31, 127];
            for _ in 0..n {
                let idx = rng.gen_range(0, mers.len() - 1);
                v.push(mers[idx]);
            }
        }
        9 => {
            // alternating even/odd primes (2 and others)
            for i in 0..n {
                if i % 2 == 0 { v.push(2); } else { v.push(pick_prime(rng)); }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(pick_prime(rng));
            }
        }
    }
    v
}

fn print_json(nums: &[i32]) {
        let nums = generate_test_case(nums.to_vec());
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
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let vals = build_mode(&mut rng, mode);
        let nums = generate_candidate(&vals);
        print_json(&nums);
    }
}
