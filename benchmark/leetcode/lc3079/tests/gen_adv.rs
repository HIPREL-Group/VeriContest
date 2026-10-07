use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 50,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
    ensures
        1 <= nums.len() <= 50,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000,
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn make_vec_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // minimum length
            let n = 1;
            let mut v = Vec::with_capacity(n);
            v.push(rng.gen_range_i32(1, 1000));
            v
        }
        1 => {
            // maximum length
            let n = 50;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            v
        }
        2 => {
            // all ones
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(1);
            }
            v
        }
        3 => {
            // all 1000
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(1000);
            }
            v
        }
        4 => {
            // single digit values only
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 9));
            }
            v
        }
        5 => {
            // two digit values
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(10, 99));
            }
            v
        }
        6 => {
            // three digit values
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(100, 999));
            }
            v
        }
        7 => {
            // values ending in 0 (test max digit computation)
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 100);
                v.push(x * 10);
            }
            v
        }
        8 => {
            // boundary: 10, 100, 1000, 9, 99, 999
            let choices: [i32; 6] = [10, 100, 1000, 9, 99, 999];
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let idx = (rng.next_u64() as usize) % choices.len();
                v.push(choices[idx]);
            }
            v
        }
        9 => {
            // values with zeros inside (like 101, 200, 305)
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let patterns: [i32; 8] = [10, 20, 100, 101, 200, 305, 500, 909];
                let idx = (rng.next_u64() as usize) % patterns.len();
                v.push(patterns[idx]);
            }
            v
        }
        _ => {
            // general random
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            v
        }
    }
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
        let vals = make_vec_mode(&mut rng, mode);
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}