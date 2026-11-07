use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100,
        vals.len() == n,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100000,
    ensures
        1 <= nums.len() <= 100,
        nums.len() == n,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == vals[i],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 100,
            vals.len() == n,
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100000,
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vals(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all equal
            let x = rng.gen_range_i32(1, 100_000);
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        2 => {
            // all max
            for _ in 0..n { v.push(100_000); }
        }
        3 => {
            // two distinct values alternating
            let a = rng.gen_range_i32(1, 100_000);
            let mut b = rng.gen_range_i32(1, 100_000);
            if b == a { b = if a == 1 { 2 } else { a - 1 }; }
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
        }
        4 => {
            // first element differs
            let base = rng.gen_range_i32(1, 100_000);
            let mut diff = rng.gen_range_i32(1, 100_000);
            if diff == base { diff = if base == 1 { 2 } else { base - 1 }; }
            v.push(diff);
            for _ in 1..n { v.push(base); }
        }
        5 => {
            // last element differs
            let base = rng.gen_range_i32(1, 100_000);
            let mut diff = rng.gen_range_i32(1, 100_000);
            if diff == base { diff = if base == 1 { 2 } else { base - 1 }; }
            for _ in 0..(n-1) { v.push(base); }
            v.push(diff);
        }
        6 => {
            // middle differs
            let base = rng.gen_range_i32(1, 100_000);
            let mut diff = rng.gen_range_i32(1, 100_000);
            if diff == base { diff = if base == 1 { 2 } else { base - 1 }; }
            let mid = n / 2;
            for i in 0..n {
                v.push(if i == mid { diff } else { base });
            }
        }
        7 => {
            // fully random
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100_000)); }
        }
        8 => {
            // small values random
            for _ in 0..n { v.push(rng.gen_range_i32(1, 5)); }
        }
        9 => {
            // powers of two
            let choices: [i32; 6] = [1, 2, 4, 8, 16, 32];
            for _ in 0..n {
                let idx = (rng.next_u64() as usize) % choices.len();
                v.push(choices[idx]);
            }
        }
        _ => {
            // random
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100_000)); }
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 100,
            4 => 99,
            5 => 50,
            _ => rng.gen_range_usize(1, 100),
        };
        let vals = build_vals(&mut rng, mode, n);
        let nums = generate_test_case(n, &vals);
        print_json(&nums);
    }
}