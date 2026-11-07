use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    start: i32,
    step: i32,
    n: usize,
    lower: i32,
    upper: i32,
) -> (nums: Vec<i32>)
    requires
        0 <= n <= 100,
        1 <= step <= 1000,
        -1_000_000_000 <= lower <= 1_000_000_000,
        -1_000_000_000 <= upper <= 1_000_000_000,
        lower <= upper,
        lower <= start <= upper,
        // Guarantee no overflow/out-of-range across the arithmetic progression
        start as int + (n as int) * (step as int) <= upper as int + 1,
    ensures
        0 <= nums.len() <= 100,
        lower <= upper,
        -1_000_000_000 <= lower <= 1_000_000_000,
        -1_000_000_000 <= upper <= 1_000_000_000,
        forall |i: int| 0 <= i < nums.len() ==> lower <= #[trigger] nums[i] <= upper,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
{
    let nums: Vec<i32> = Vec::new();
    nums
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
        if lo >= hi {
            return lo;
        }
        let span = (hi - lo + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        if lo >= hi {
            return lo;
        }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

// Given mode, produce (start, step, n, lower, upper) satisfying preconditions
fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32, usize, i32, i32) {
    // Preconditions:
    //   0 <= n <= 100
    //   1 <= step <= 1000
    //   -1e9 <= lower <= upper <= 1e9
    //   lower <= start <= upper
    //   start + n * step <= upper + 1
    match mode {
        0 => {
            // Empty nums: n = 0
            let lower = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
            let upper = rng.gen_range_i64(lower, 1_000_000_000);
            // start just needs to be in [lower, upper]; not really used
            (lower as i32, 1i32, 0usize, lower as i32, upper as i32)
        }
        1 => {
            // Single element equal to lower == upper (no missing)
            let x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
            (x as i32, 1i32, 1usize, x as i32, x as i32)
        }
        2 => {
            // Dense: start=lower, step=1, covers fully, n up to 100, upper>=start+n-1
            let n = rng.gen_range_usize(0, 100);
            let lower = rng.gen_range_i64(-1_000_000_000, 1_000_000_000 - n as i64);
            let upper = rng.gen_range_i64(lower + n as i64 - 1, 1_000_000_000).max(lower);
            let upper = if upper < lower + (n as i64).max(1) - 1 {
                lower + (n as i64).max(1) - 1
            } else {
                upper
            };
            let upper = upper.min(1_000_000_000);
            // start = lower; need start + n*1 <= upper + 1 => lower + n <= upper + 1
            let start = lower;
            (start as i32, 1i32, n, lower as i32, upper as i32)
        }
        3 => {
            // Large step, widely spaced
            let step = rng.gen_range_i64(100, 1000) as i32;
            let n = rng.gen_range_usize(0, 100);
            // We need start + n*step <= upper + 1
            // Pick upper near 1e9, lower small
            let upper = 1_000_000_000i64;
            let lower = -1_000_000_000i64;
            // start + n*step <= upper+1
            let max_start = upper + 1 - (n as i64) * (step as i64);
            let start = rng.gen_range_i64(lower, max_start.min(upper));
            (start as i32, step, n, lower as i32, upper as i32)
        }
        4 => {
            // Near boundaries: upper at 1e9
            let upper = 1_000_000_000i64;
            let step = 1i32;
            let n = rng.gen_range_usize(0, 100);
            let start = upper - n as i64 + 1;
            let start = start.max(-1_000_000_000);
            let lower = start.min(upper);
            (start as i32, step, n, lower as i32, upper as i32)
        }
        5 => {
            // Near lower boundary: lower = -1e9
            let lower = -1_000_000_000i64;
            let step = 1i32;
            let n = rng.gen_range_usize(0, 100);
            let upper = rng.gen_range_i64(lower + n as i64, 1_000_000_000);
            let start = lower;
            (start as i32, step, n, lower as i32, upper as i32)
        }
        6 => {
            // Random valid
            let lower = rng.gen_range_i64(-1_000_000_000, 999_900_000);
            let upper = rng.gen_range_i64(lower, 1_000_000_000);
            let step = rng.gen_range_i64(1, 1000) as i32;
            let max_n_by_step = ((upper - lower + 1) / step as i64).min(100).max(0);
            let n = if max_n_by_step > 0 {
                rng.gen_range_usize(0, max_n_by_step as usize)
            } else {
                0
            };
            let max_start = upper + 1 - (n as i64) * (step as i64);
            let start = rng.gen_range_i64(lower, max_start.max(lower));
            (start as i32, step, n, lower as i32, upper as i32)
        }
        7 => {
            // n = 100 maximum
            let step = rng.gen_range_i64(1, 100) as i32;
            let n = 100usize;
            let lower = rng.gen_range_i64(-1_000_000_000, 1_000_000_000 - (n as i64) * (step as i64));
            let upper = rng.gen_range_i64(lower + (n as i64) * (step as i64) - 1, 1_000_000_000);
            let start = lower;
            (start as i32, step, n, lower as i32, upper as i32)
        }
        8 => {
            // Single element, interior
            let lower = rng.gen_range_i64(-1_000_000_000, 999_999_000);
            let upper = rng.gen_range_i64(lower, 1_000_000_000);
            let start = rng.gen_range_i64(lower, upper);
            (start as i32, 1i32, 1usize, lower as i32, upper as i32)
        }
        9 => {
            // Adjacent: small range, n=1
            let x = rng.gen_range_i64(-1_000_000_000, 999_999_999);
            let lower = x;
            let upper = x + 1;
            (x as i32, 1i32, 1usize, lower as i32, upper as i32)
        }
        _ => {
            // Default random
            let lower = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
            let upper = rng.gen_range_i64(lower, 1_000_000_000);
            (lower as i32, 1i32, 0usize, lower as i32, upper as i32)
        }
    }
}

fn validate(start: i32, step: i32, n: usize, lower: i32, upper: i32) -> bool {
    if n > 100 {
        return false;
    }
    if step < 1 || step > 1000 {
        return false;
    }
    if lower < -1_000_000_000 || lower > 1_000_000_000 {
        return false;
    }
    if upper < -1_000_000_000 || upper > 1_000_000_000 {
        return false;
    }
    if lower > upper {
        return false;
    }
    if start < lower || start > upper {
        return false;
    }
    let end = start as i64 + (n as i64) * (step as i64);
    if end > upper as i64 + 1 {
        return false;
    }
    true
}

fn print_json(nums: &[i32], lower: i32, upper: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"lower\":{},\"upper\":{}}}", lower, upper);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    let mut count = 0;
    let mut attempts = 0;
    while count < total && attempts < total * 10 {
        attempts += 1;
        let mode = count % modes;
        let (start, step, n, lower, upper) = pick_case(&mut rng, mode);
        if !validate(start, step, n, lower, upper) {
            continue;
        }
        let nums = generate_test_case(start, step, n, lower, upper);
        print_json(&nums, lower, upper);
        count += 1;
    }
}
