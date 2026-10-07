use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 10_000,
        forall |i: int| 0 <= i < values.len() ==>
            -1_000_000_000 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 10_000,
        forall |i: int| 1 <= i < nums.len() ==>
            -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==>
                -1_000_000_000 <= #[trigger] values[k] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    nums
}

}

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

fn clamp_values(v: &mut Vec<i32>) {
    for x in v.iter_mut() {
        if *x > 1_000_000_000 {
            *x = 1_000_000_000;
        } else if *x < -1_000_000_000 {
            *x = -1_000_000_000;
        }
    }
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    match mode {
        0 => {
            // tiny distinct
            let n = 1 + (t % 5);
            for i in 0..n {
                v.push(i as i32);
            }
        }
        1 => {
            // tiny with duplicate
            let n = 2 + (t % 5);
            for i in 0..n {
                v.push((i % 2) as i32);
            }
        }
        2 => {
            // all same
            let n = rng.gen_range_usize(1, 100);
            let val = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            for _ in 0..n {
                v.push(val);
            }
        }
        3 => {
            // all distinct, random
            let n = rng.gen_range_usize(1, 500);
            let mut seen = std::collections::HashSet::new();
            while v.len() < n {
                let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
                if seen.insert(x) {
                    v.push(x);
                }
            }
        }
        4 => {
            // duplicate at extremes (first and last)
            let n = rng.gen_range_usize(2, 300);
            let dup = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            v.push(dup);
            let mut seen = std::collections::HashSet::new();
            seen.insert(dup);
            while v.len() < n - 1 {
                let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
                if seen.insert(x) {
                    v.push(x);
                }
            }
            v.push(dup);
        }
        5 => {
            // max size all distinct (0..9999)
            for i in 0..10_000 {
                v.push(i as i32 - 5000);
            }
        }
        6 => {
            // max size with one duplicate pair
            for i in 0..10_000 {
                v.push(i as i32 - 5000);
            }
            let j = rng.gen_range_usize(0, 9999);
            let k = rng.gen_range_usize(0, 9999);
            if j != k {
                v[j] = v[k];
            } else {
                v[0] = v[9999];
            }
        }
        7 => {
            // boundary values
            let n = rng.gen_range_usize(2, 50);
            for _ in 0..n {
                let pick = rng.next_u64() % 4;
                let x = match pick {
                    0 => 1_000_000_000,
                    1 => -1_000_000_000,
                    2 => 0,
                    _ => rng.gen_range_i32(-1_000_000_000, 1_000_000_000),
                };
                v.push(x);
            }
        }
        8 => {
            // sorted with adjacent duplicates
            let n = rng.gen_range_usize(2, 200);
            let mut cur: i32 = rng.gen_range_i32(-500_000_000, 0);
            for i in 0..n {
                if i > 0 && rng.next_u64() % 3 == 0 {
                    // duplicate
                } else {
                    cur = cur.saturating_add(rng.gen_range_i32(1, 100));
                }
                v.push(cur);
            }
        }
        9 => {
            // negatives only
            let n = rng.gen_range_usize(1, 200);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, -1));
            }
        }
        _ => {
            // random mix
            let n = rng.gen_range_usize(1, 1000);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
        }
    }
    if v.is_empty() {
        v.push(0);
    }
    if v.len() > 10_000 {
        v.truncate(10_000);
    }
    clamp_values(&mut v);
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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
        let values = build(&mut rng, mode, t);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}