use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000000000,
    ensures
        1 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000000000,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000000000,
        decreases n - i,
    {
        nums.push(values[i]);
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn digit_sum_u(mut x: i32) -> i32 {
    let mut s = 0;
    while x > 0 {
        s += x % 10;
        x /= 10;
    }
    s
}

fn build_with_digit_sum(rng: &mut Rng, target_ds: i32, max_val: i32) -> i32 {
    // Try to find a random number with given digit sum
    for _ in 0..100 {
        let v = rng.gen_range_i32(1, max_val);
        if digit_sum_u(v) == target_ds {
            return v;
        }
    }
    // Fallback: construct
    let mut remaining = target_ds;
    let mut val: i64 = 0;
    let mut mult: i64 = 1;
    while remaining > 0 {
        let d = if remaining > 9 { 9 } else { remaining };
        val += (d as i64) * mult;
        mult *= 10;
        remaining -= d;
        if val > max_val as i64 {
            return 1;
        }
    }
    if val < 1 || val > max_val as i64 { 1 } else { val as i32 }
}

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut values: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // random
            for _ in 0..n {
                values.push(rng.gen_range_i32(1, 1_000_000_000));
            }
        }
        1 => {
            // all same digit sum (small)
            for _ in 0..n {
                let v = build_with_digit_sum(rng, 9, 1_000_000_000);
                values.push(v);
            }
        }
        2 => {
            // all distinct digit sums (use small numbers 1..=n, if n<=45)
            for i in 0..n {
                values.push(((i % 9) + 1) as i32);
            }
        }
        3 => {
            // all 1's
            for _ in 0..n {
                values.push(1);
            }
        }
        4 => {
            // max values
            for _ in 0..n {
                values.push(1_000_000_000);
            }
        }
        5 => {
            // pairs with matching digit sum
            let mut i = 0;
            while i < n {
                let ds = rng.gen_range_i32(1, 40);
                let v = build_with_digit_sum(rng, ds, 1_000_000_000);
                values.push(v);
                if i + 1 < n {
                    let v2 = build_with_digit_sum(rng, ds, 1_000_000_000);
                    values.push(v2);
                }
                i += 2;
            }
        }
        6 => {
            // powers of 10
            for i in 0..n {
                let p = (i % 10) as u32;
                let mut v: i64 = 1;
                for _ in 0..p { v *= 10; }
                if v > 1_000_000_000 { v = 1_000_000_000; }
                values.push(v as i32);
            }
        }
        7 => {
            // only two values with same digit sum
            for i in 0..n {
                if i == 0 { values.push(18); }
                else if i == n/2 { values.push(81); }
                else {
                    let mut v = rng.gen_range_i32(1, 1_000_000_000);
                    while digit_sum_u(v) == 9 {
                        v = rng.gen_range_i32(1, 1_000_000_000);
                    }
                    values.push(v);
                }
            }
        }
        8 => {
            // small size 1
            values.push(rng.gen_range_i32(1, 1_000_000_000));
        }
        9 => {
            // near-max sum candidates
            for _ in 0..n {
                let choice = rng.gen_range_usize(0, 2);
                let v = match choice {
                    0 => 999_999_999,
                    1 => 1_000_000_000,
                    _ => 900_000_000,
                };
                values.push(v);
            }
        }
        _ => {
            for _ in 0..n {
                values.push(rng.gen_range_i32(1, 100));
            }
        }
    }
    // ensure length exactly n
    while values.len() < n {
        values.push(1);
    }
    values.truncate(n);
    // ensure bounds
    for v in values.iter_mut() {
        if *v < 1 { *v = 1; }
        if *v > 1_000_000_000 { *v = 1_000_000_000; }
    }
    values
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 100),
            1 => rng.gen_range_usize(2, 50),
            2 => rng.gen_range_usize(1, 9),
            3 => rng.gen_range_usize(1, 20),
            4 => rng.gen_range_usize(2, 20),
            5 => rng.gen_range_usize(2, 200),
            6 => rng.gen_range_usize(1, 50),
            7 => rng.gen_range_usize(2, 30),
            8 => 1,
            9 => rng.gen_range_usize(2, 100),
            _ => rng.gen_range_usize(1, 50),
        };
        let values = make_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}