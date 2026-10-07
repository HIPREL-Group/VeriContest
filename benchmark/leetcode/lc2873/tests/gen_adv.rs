use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        3 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000000,
{
    let n = if values.len() < 3 { 3usize }
            else if values.len() > 100 { 100usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            3 <= n <= 100,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 1000000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 1000000 { 1000000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(
    vals: &Vec<i32>,
    i_val: usize,
    j_val: usize,
    k_val: usize,
    acc_val: i64,
) -> (result: (Vec<i32>, usize, usize, usize, i64))
    requires
        3 <= vals.len() <= 100,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1_000_000,
    ensures
        ({
            let (nums, i, j, k, acc) = result;
            &&& 3 <= nums.len() <= 100
            &&& forall|x: int| 0 <= x < nums.len() ==> 1 <= #[trigger] nums[x] <= 1_000_000
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < vals.len()
        invariant
            0 <= idx <= vals.len(),
            nums.len() == idx,
            forall|x: int| 0 <= x < idx as int ==> 1 <= #[trigger] nums[x] <= 1_000_000,
            forall|x: int| 0 <= x < vals.len() ==> 1 <= #[trigger] vals[x] <= 1_000_000,
        decreases vals.len() - idx,
    {
        nums.push(vals[idx]);
        idx += 1;
    }
    (nums, i_val, j_val, k_val, acc_val)
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build_vals(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000));
            }
        }
        1 => {
            for _ in 0..n { v.push(1); }
        }
        2 => {
            for _ in 0..n { v.push(1_000_000); }
        }
        3 => {
            // decreasing
            for i in 0..n {
                let val = (1_000_000 - (i as i32) * 10).max(1);
                v.push(val);
            }
        }
        4 => {
            // increasing
            for i in 0..n {
                let val = ((i as i32) * 10 + 1).min(1_000_000);
                v.push(val);
            }
        }
        5 => {
            // big dip in middle: large, small, large pattern
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(1_000_000);
                } else {
                    v.push(1);
                }
            }
        }
        6 => {
            // all small making product small
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
        }
        7 => {
            // first large, rest small
            v.push(1_000_000);
            for _ in 1..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        8 => {
            // last large, rest small
            for _ in 0..n-1 {
                v.push(rng.gen_range_i32(1, 100));
            }
            v.push(1_000_000);
        }
        9 => {
            // all same random
            let x = rng.gen_range_i32(1, 1_000_000);
            for _ in 0..n { v.push(x); }
        }
        _ => {
            // designed: nums[0] large, nums[1] small, nums[last] large
            v.push(1_000_000);
            v.push(1);
            for _ in 2..n-1 {
                v.push(rng.gen_range_i32(1, 500_000));
            }
            if n >= 3 {
                v.push(1_000_000);
            }
        }
    }
    while v.len() < n {
        v.push(1);
    }
    v.truncate(n);
    v
}

fn print_json(nums: &[i32], i: usize, j: usize, k: usize, acc: i64) {
    let nums = generate_test_case(nums.to_vec());
    print!("{{\"nums\":[");
    for idx in 0..nums.len() {
        if idx > 0 { print!(","); }
        print!("{}", nums[idx]);
    }
    println!("],\"i\":{},\"j\":{},\"k\":{},\"acc\":{}}}", i, j, k, acc);
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
            0 => 3 + (t % 10),
            1 => 3,
            2 => 100,
            3 => 50,
            4 => 50,
            5 => 20,
            6 => 100,
            7 => 10,
            8 => 10,
            9 => 3 + (t % 50),
            _ => 3 + (t % 97),
        };
        let n = n.max(3).min(100);

        let vals = build_vals(&mut rng, mode, n);

        // for solve_k signature: pick i < j < k typically
        let i_val: usize = 0;
        let j_val: usize = 1;
        let k_val: usize = 2;
        let acc_val: i64 = 0;

        let (nums, i, j, k, acc) = generate_candidate(&vals, i_val, j_val, k_val, acc_val);
        print_json(&nums, i, j, k, acc);
    }
}
