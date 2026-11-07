use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
    k_val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 200,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100,
        1 <= k_val <= 99,
    ensures
        1 <= result.0.len() <= 200,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 99,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            nums.len() == i,
            forall |j: int| 0 <= j < vals.len() ==> 1 <= #[trigger] vals[j] <= 100,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 100,
        decreases n - i,
    {
        nums.push(vals[i]);
        i = i + 1;
    }
    (nums, k_val)
}

}

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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // tiny random
            let n = rng.gen_range_usize(1, 5);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            let k = rng.gen_range_i32(1, 99);
            (v, k)
        }
        1 => {
            // max length random
            let n = 200;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            let k = rng.gen_range_i32(1, 99);
            (v, k)
        }
        2 => {
            // all same value
            let n = rng.gen_range_usize(1, 200);
            let val = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(val); }
            let k = rng.gen_range_i32(1, 99);
            (v, k)
        }
        3 => {
            // two-value alternating with diff = k
            let n = rng.gen_range_usize(2, 200);
            let k = rng.gen_range_i32(1, 99);
            let a = rng.gen_range_i32(1, 100 - k);
            let b = a + k;
            let mut v = Vec::new();
            for i in 0..n { v.push(if i % 2 == 0 { a } else { b }); }
            (v, k)
        }
        4 => {
            // single element
            let mut v = Vec::new();
            v.push(rng.gen_range_i32(1, 100));
            (v, rng.gen_range_i32(1, 99))
        }
        5 => {
            // k at boundary (1)
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            (v, 1)
        }
        6 => {
            // k at boundary (99)
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            (v, 99)
        }
        7 => {
            // only 1 and 100
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(if rng.next_u64() % 2 == 0 { 1 } else { 100 });
            }
            let k = rng.gen_range_i32(1, 99);
            (v, k)
        }
        8 => {
            // sequential
            let n = rng.gen_range_usize(1, 100);
            let start = rng.gen_range_i32(1, 100 - n as i32 + 1);
            let mut v = Vec::new();
            for i in 0..n { v.push(start + i as i32); }
            let k = rng.gen_range_i32(1, 99);
            (v, k)
        }
        9 => {
            // many duplicates of few values
            let n = rng.gen_range_usize(10, 200);
            let vals = [2, 5, 7, 10];
            let mut v = Vec::new();
            for _ in 0..n { v.push(vals[(rng.next_u64() as usize) % vals.len()]); }
            let k = rng.gen_range_i32(1, 99);
            (v, k)
        }
        _ => {
            let n = rng.gen_range_usize(50, 200);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            let k = rng.gen_range_i32(1, 99);
            (v, k)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (vals, k) = build_case(&mut rng, mode, t);
        // sanity clamp
        let mut clean: Vec<i32> = Vec::new();
        for x in vals.iter() {
            let xx = if *x < 1 { 1 } else if *x > 100 { 100 } else { *x };
            clean.push(xx);
        }
        if clean.is_empty() { clean.push(1); }
        if clean.len() > 200 { clean.truncate(200); }
        let kk = if k < 1 { 1 } else if k > 99 { 99 } else { k };
        let (nums, kout) = generate_test_case(&clean, kk);
        print_json(&nums, kout);
    }
}