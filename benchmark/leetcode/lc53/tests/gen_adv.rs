use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 100_000,
        forall |i: int| 0 <= i < vals.len() ==> -10_000 <= #[trigger] vals[i] <= 10_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> -10_000 <= #[trigger] vals[k] <= 10_000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == vals[k],
            forall |k: int| 0 <= k < i as int ==> -10_000 <= #[trigger] nums[k] <= 10_000,
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
        Self { state: seed.wrapping_add(1) }
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

fn make_vals_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // random
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10_000, 10_000));
            }
        }
        1 => {
            // all positive
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10_000));
            }
        }
        2 => {
            // all negative
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10_000, -1));
            }
        }
        3 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        4 => {
            // all same value
            let x = rng.gen_range_i32(-10_000, 10_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        5 => {
            // alternating +/-
            for i in 0..n {
                if i % 2 == 0 { v.push(10_000); } else { v.push(-10_000); }
            }
        }
        6 => {
            // large negative surrounding a positive block
            for i in 0..n {
                if i >= n/3 && i < 2*n/3 {
                    v.push(rng.gen_range_i32(1, 10_000));
                } else {
                    v.push(rng.gen_range_i32(-10_000, -1));
                }
            }
        }
        7 => {
            // extremes only
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(10_000); } else { v.push(-10_000); }
            }
        }
        8 => {
            // single element
            v.push(rng.gen_range_i32(-10_000, 10_000));
        }
        9 => {
            // max length worst-case all -10000 then single 10000
            for _ in 0..n.saturating_sub(1) {
                v.push(-10_000);
            }
            if n >= 1 { v.push(10_000); }
        }
        _ => {
            // sparse pattern
            for i in 0..n {
                if i % 5 == 0 { v.push(rng.gen_range_i32(-10_000, 10_000)); }
                else { v.push(0); }
            }
        }
    }
    // ensure length exactly n
    while v.len() < n { v.push(0); }
    v.truncate(n);
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
            0 => 1 + (t % 50),
            1 => 2 + (t % 100),
            2 => 1 + (t % 80),
            3 => 1 + (t % 20),
            4 => 1 + (t % 30),
            5 => 2 + (t % 60),
            6 => 3 + (t % 90),
            7 => 2 + (t % 40),
            8 => 1,
            9 => if t % 3 == 0 { 100_000 } else { 100 + (t % 50) },
            _ => 500 + (t % 300),
        };

        let vals = make_vals_mode(&mut rng, mode, n);
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}