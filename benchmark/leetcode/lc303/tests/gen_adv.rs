use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 10000,
        forall |i: int| 0 <= i < vals.len() ==> -100000 <= #[trigger] vals[i] <= 100000,
    ensures
        1 <= nums.len() <= 10000,
        nums.len() == vals.len(),
        forall |i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums[i] <= 100000,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == vals.len(),
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < vals.len() ==> -100000 <= #[trigger] vals[i] <= 100000,
            forall |i: int| 0 <= i < k as int ==> nums[i] == vals[i],
            forall |i: int| 0 <= i < k as int ==> -100000 <= #[trigger] nums[i] <= 100000,
        decreases n - k,
    {
        nums.push(vals[k]);
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vals(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // all max positive
            for _ in 0..n { v.push(100000); }
        }
        2 => {
            // all max negative
            for _ in 0..n { v.push(-100000); }
        }
        3 => {
            // alternating max +/-
            for i in 0..n {
                v.push(if i % 2 == 0 { 100000 } else { -100000 });
            }
        }
        4 => {
            // sequential small
            for i in 0..n {
                v.push((i as i32) - (n as i32) / 2);
            }
        }
        5 => {
            // single value (n=1 extreme tested elsewhere); random small
            for _ in 0..n { v.push(rng.gen_range_i32(-10, 10)); }
        }
        6 => {
            // random full-range
            for _ in 0..n { v.push(rng.gen_range_i32(-100000, 100000)); }
        }
        7 => {
            // all same random
            let x = rng.gen_range_i32(-100000, 100000);
            for _ in 0..n { v.push(x); }
        }
        8 => {
            // mostly zero with one big
            for _ in 0..n { v.push(0); }
            if n > 0 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = 100000;
            }
        }
        9 => {
            // boundary: -1, 0, 1 pattern
            for i in 0..n {
                let r = i % 3;
                v.push(if r == 0 { -1 } else if r == 1 { 0 } else { 1 });
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(-100000, 100000)); }
        }
    }
    v
}

fn print_json(nums: &[i32], left: i32, right: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"left\":{},\"right\":{}}}", left, right);
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

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 13 {
            0 => 1usize,
            1 => 2,
            2 => 3,
            3 => 10,
            4 => 100,
            5 => 1000,
            6 => 10000,
            7 => 5000,
            8 => 500,
            9 => 50,
            10 => 17,
            11 => 9999,
            _ => {
                let mut x = rng.gen_range_usize(1, 10000);
                if x < 1 { x = 1; }
                x
            }
        };
        let vals = build_vals(&mut rng, mode, n);
        let nums = generate_test_case(&vals);
        let nlen = nums.len();
        let last = (nlen.saturating_sub(1)) as i32;
        let left = if nlen == 0 {
            0i32
        } else {
            rng.gen_range_usize(0, nlen - 1) as i32
        };
        let right = if nlen == 0 {
            0i32
        } else {
            rng.gen_range_usize(left as usize, nlen - 1) as i32
        };
        let left = left.min(last).max(0);
        let right = right.max(left).min(last);
        print_json(&nums, left, right);
    }
}