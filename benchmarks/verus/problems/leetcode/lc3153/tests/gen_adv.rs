use vstd::prelude::*;

verus! {

pub open spec fn digit_count(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 } else if n < 10 { 1 } else { 1 + digit_count(n / 10) }
}
fn digit_width(n: i32) -> (result: u32)
    requires 1 <= n <= 999999999,
    ensures result == digit_count(n as int), 1 <= result <= n,
    decreases n,
{
    if n < 10 { 1 } else { 1 + digit_width(n / 10) }
}
pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures 2 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] < 1000000000,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() ==>
            digit_count(#[trigger] result[i] as int) == digit_count(#[trigger] result[j] as int),
{
    let n = if raw.len() < 2 { 2usize } else if raw.len() > 100000 { 100000usize } else { raw.len() };
    let first = if raw.len() == 0 { 1 } else { raw[0] };
    let first = if first < 1 { 1 } else if first > 999999999 { 999999999 } else { first };
    let width = digit_width(first);
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant i <= n, 2 <= n <= 100000, result.len() == i,
            1 <= first <= 999999999, width == digit_count(first as int),
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] < 1000000000,
            forall|j: int| 0 <= j < result.len() ==> digit_count(#[trigger] result[j] as int) == width,
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { first };
        let v = if v < 1 { 1 } else if v > 999999999 { 999999999 } else { v };
        let v = if digit_width(v) == width { v } else { first };
        result.push(v);
        i += 1;
    }
    result
}


pub fn generate_candidate(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= vals.len() <= 100000,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] < 1_000_000_000,
    ensures
        2 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] < 1_000_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            2 <= n <= 100000,
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] < 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] < 1_000_000_000,
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

// Generate a number with exactly `digits` digits, value in [10^(d-1), 10^d - 1]
fn pow10(d: usize) -> i64 {
    let mut r: i64 = 1;
    for _ in 0..d {
        r *= 10;
    }
    r
}

fn gen_num_with_digits(rng: &mut Rng, digits: usize) -> i32 {
    // digits in 1..=9 (since < 10^9)
    let lo = if digits == 1 { 1 } else { pow10(digits - 1) };
    let hi = pow10(digits) - 1;
    rng.gen_range_i64(lo, hi) as i32
}

fn adversarial_case(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n: usize = match mode {
        0 => 2,
        1 => 2 + (t % 5),
        2 => 100_000,
        3 => 100,
        4 => 1000,
        5 => 10_000,
        6 => 50 + (t % 50),
        7 => 3,
        8 => 2,
        9 => 500 + (t % 200),
        _ => 20 + (t % 80),
    };

    // choose digit count 1..=9
    let digits: usize = match mode {
        0 => 1,
        1 => 9,
        2 => 9,
        3 => 1,
        4 => 2,
        5 => ((t % 9) + 1),
        6 => 5,
        7 => 9,
        8 => 9,
        9 => ((t % 8) + 2),
        _ => ((t % 9) + 1),
    };

    let mut vals: Vec<i32> = Vec::with_capacity(n);

    match mode {
        // All same
        3 => {
            let v = gen_num_with_digits(rng, digits);
            for _ in 0..n {
                vals.push(v);
            }
        }
        // Only two distinct values alternating
        4 => {
            let v1 = gen_num_with_digits(rng, digits);
            let v2 = gen_num_with_digits(rng, digits);
            for i in 0..n {
                if i % 2 == 0 { vals.push(v1); } else { vals.push(v2); }
            }
        }
        // Min boundary
        0 => {
            vals.push(1);
            vals.push(9);
        }
        // Max boundary, all 999999999
        2 => {
            for _ in 0..n {
                vals.push(999_999_999);
            }
        }
        // Large n random max digits
        8 => {
            vals.push(100_000_000);
            vals.push(999_999_999);
        }
        _ => {
            for _ in 0..n {
                vals.push(gen_num_with_digits(rng, digits));
            }
        }
    }

    // Ensure length bounds
    while vals.len() < 2 {
        vals.push(gen_num_with_digits(rng, digits));
    }
    if vals.len() > 100_000 {
        vals.truncate(100_000);
    }
    vals
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let vals = adversarial_case(&mut rng, mode, t);
        // Validate
        let mut ok = vals.len() >= 2 && vals.len() <= 100_000;
        for &v in &vals {
            if v < 1 || v >= 1_000_000_000 {
                ok = false;
                break;
            }
        }
        if !ok {
            let mut fallback: Vec<i32> = Vec::new();
            fallback.push(1);
            fallback.push(9);
            let nums = generate_candidate(&fallback);
            print_json(&nums);
            continue;
        }
        let nums = generate_candidate(&vals);
        print_json(&nums);
    }
}
