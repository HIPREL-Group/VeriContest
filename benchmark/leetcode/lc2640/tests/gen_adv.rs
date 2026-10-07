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
            n == values.len(),
            0 <= i <= n,
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

fn build(values: Vec<i32>) -> Vec<i32> {
    // Clamp defensively
    let mut v = values;
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 1_000_000_000 { *x = 1_000_000_000; }
    }
    if v.is_empty() { v.push(1); }
    if v.len() > 100000 { v.truncate(100000); }
    generate_test_case(&v)
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn adversarial(mode: usize, rng: &mut Rng, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_range_i32(1, 1_000_000_000)]
        }
        1 => {
            // all same value
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(1, 1_000_000_000);
            vec![v; n]
        }
        2 => {
            // strictly increasing
            let n = rng.gen_range_usize(2, 50);
            let mut res = Vec::with_capacity(n);
            let mut cur: i32 = 1;
            for _ in 0..n {
                res.push(cur);
                cur = cur.saturating_add(rng.gen_range_i32(1, 100));
                if cur > 1_000_000_000 { cur = 1_000_000_000; }
            }
            res
        }
        3 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 50);
            let mut res = Vec::with_capacity(n);
            let mut cur: i32 = 1_000_000_000;
            for _ in 0..n {
                res.push(cur);
                let dec = rng.gen_range_i32(1, 100);
                cur = if cur > dec { cur - dec } else { 1 };
            }
            res
        }
        4 => {
            // maximum boundary values
            let n = rng.gen_range_usize(1, 100);
            vec![1_000_000_000; n]
        }
        5 => {
            // minimum boundary values
            let n = rng.gen_range_usize(1, 100);
            vec![1; n]
        }
        6 => {
            // large n
            let n = 100000;
            let mut res = Vec::with_capacity(n);
            for _ in 0..n {
                res.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            res
        }
        7 => {
            // large n with all 1e9 (overflow test)
            vec![1_000_000_000; 100000]
        }
        8 => {
            // leetcode example 1
            vec![2, 3, 7, 5, 10]
        }
        9 => {
            // leetcode example 2
            vec![1, 1, 2, 4, 8, 16]
        }
        10 => {
            // alternating big/small
            let n = rng.gen_range_usize(2, 100);
            let mut res = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    res.push(1_000_000_000);
                } else {
                    res.push(1);
                }
            }
            res
        }
        11 => {
            // peak in middle
            let n = rng.gen_range_usize(3, 50);
            let mut res = Vec::with_capacity(n);
            let mid = n / 2;
            for i in 0..n {
                let v = if i == mid { 1_000_000_000 } else { rng.gen_range_i32(1, 1000) };
                res.push(v);
            }
            res
        }
        _ => {
            // random
            let n = rng.gen_range_usize(1, 200);
            let mut res = Vec::with_capacity(n);
            for _ in 0..n {
                res.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            res
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 13usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let values = adversarial(mode, &mut rng, t);
        let nums = build(values);
        print_json(&nums);
    }
}