use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= k <= n,
            nums.len() == k,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
            forall|i: int| 0 <= i < k as int ==> #[trigger] nums[i] == values[i],
            forall|i: int| 0 <= i < k as int ==> 1 <= #[trigger] nums[i] <= 100,
        decreases n - k,
    {
        nums.push(values[k]);
        k = k + 1;
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all equal
            let x = rng.gen_range_i32(1, 100);
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        2 => {
            // all max
            for _ in 0..n { v.push(100); }
        }
        3 => {
            // one min rest max
            for _ in 0..n { v.push(100); }
            if n > 0 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = 1;
            }
        }
        4 => {
            // one max rest min
            for _ in 0..n { v.push(1); }
            if n > 0 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = 100;
            }
        }
        5 => {
            // sorted ascending
            for i in 0..n {
                let val = ((i % 100) as i32) + 1;
                v.push(val);
            }
        }
        6 => {
            // sorted descending
            for i in 0..n {
                let val = 100 - ((i % 100) as i32);
                v.push(val);
            }
        }
        7 => {
            // mix of 1 and 100
            for _ in 0..n {
                let b = rng.next_u64() % 2;
                v.push(if b == 0 { 1 } else { 100 });
            }
        }
        8 => {
            // many duplicates of median-ish
            let base = rng.gen_range_i32(40, 60);
            for _ in 0..n {
                let delta = rng.gen_range_i32(-5, 5);
                let mut x = base + delta;
                if x < 1 { x = 1; }
                if x > 100 { x = 100; }
                v.push(x);
            }
        }
        9 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        _ => {
            // small values
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
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
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 10),
            1 => 100,
            2 => 100,
            3 => 50,
            4 => 50,
            5 => 100,
            6 => 100,
            7 => 2 + (t % 98),
            8 => 10 + (t % 90),
            9 => 1 + (t % 100),
            _ => {
                let r = rng.gen_range_usize(1, 100);
                r
            }
        };
        let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
        let values = build_values(&mut rng, mode, n);
        // Ensure bounds (defensive clamp already done in modes).
        let mut clamped: Vec<i32> = Vec::with_capacity(values.len());
        for &x in &values {
            let y = if x < 1 { 1 } else if x > 100 { 100 } else { x };
            clamped.push(y);
        }
        let nums = generate_test_case(&clamped);
        print_json(&nums);
    }
}