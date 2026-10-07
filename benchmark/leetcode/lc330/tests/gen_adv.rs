use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    n_val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 1000,
        1 <= n_val <= 2147483647,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10000,
        forall|i: int, j: int| 0 <= i < j < values.len() ==> values[i] <= values[j],
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1 <= 2147483647,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < values.len()
        invariant
            0 <= k <= values.len(),
            nums.len() == k,
            forall|i: int| 0 <= i < k as int ==> #[trigger] nums[i] == values[i],
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10000,
            forall|i: int, j: int| 0 <= i < j < values.len() ==> values[i] <= values[j],
        decreases values.len() - k,
    {
        nums.push(values[k]);
        k = k + 1;
    }
    (nums, n_val)
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

fn make_sorted(rng: &mut Rng, len: usize, maxv: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i32(1, maxv));
    }
    v.sort();
    v
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // Random small
            let len = rng.gen_range_usize(1, 10);
            let nums = make_sorted(rng, len, 20);
            let n = rng.gen_range_i32(1, 50);
            (nums, n)
        }
        1 => {
            // Single element
            let v = rng.gen_range_i32(1, 10000);
            let n = rng.gen_range_i32(1, 2147483647);
            (vec![v], n)
        }
        2 => {
            // [1] with large n
            (vec![1], 2147483647)
        }
        3 => {
            // Powers of two
            let mut v = Vec::new();
            let mut x = 1i32;
            while x <= 8192 && v.len() < 14 {
                v.push(x);
                x = x * 2;
            }
            (v, rng.gen_range_i32(1, 2147483647))
        }
        4 => {
            // All max
            let len = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..len {
                v.push(10000);
            }
            (v, rng.gen_range_i32(1, 2147483647))
        }
        5 => {
            // Length 1000
            let nums = make_sorted(rng, 1000, 10000);
            (nums, rng.gen_range_i32(1, 2147483647))
        }
        6 => {
            // Sparse gaps
            let nums = vec![1, 5, 10];
            (nums, 20)
        }
        7 => {
            // Example 1
            (vec![1, 3], 6)
        }
        8 => {
            // Example 3
            (vec![1, 2, 2], 5)
        }
        9 => {
            // Large gap first
            let v = rng.gen_range_i32(2, 100);
            (vec![v], rng.gen_range_i32(1, 1000))
        }
        10 => {
            // n = 1
            let len = rng.gen_range_usize(1, 5);
            let nums = make_sorted(rng, len, 10000);
            (nums, 1)
        }
        11 => {
            // Duplicates
            let val = rng.gen_range_i32(1, 100);
            let len = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for _ in 0..len {
                v.push(val);
            }
            (v, rng.gen_range_i32(1, 10000))
        }
        12 => {
            // Medium random
            let len = rng.gen_range_usize(1, 50);
            let nums = make_sorted(rng, len, 10000);
            let n = rng.gen_range_i32(1, 1000000);
            (nums, n)
        }
        _ => {
            // Fibonacci-like
            let mut v = vec![1i32, 2];
            while v.len() < 10 {
                let a = v[v.len() - 1];
                let b = v[v.len() - 2];
                let s = a as i64 + b as i64;
                if s > 10000 { break; }
                v.push(s as i32);
            }
            (v, rng.gen_range_i32(1, 2147483647))
        }
    }
}

fn print_json(nums: &[i32], n: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"n\":{}}}", n);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 14usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (values, n_val) = build(&mut rng, mode, t);
        if values.is_empty() || values.len() > 1000 { continue; }
        let mut ok = true;
        for &x in &values {
            if x < 1 || x > 10000 { ok = false; break; }
        }
        if !ok { continue; }
        for i in 1..values.len() {
            if values[i-1] > values[i] { ok = false; break; }
        }
        if !ok { continue; }
        if n_val < 1 { continue; }
        let (nums, n) = generate_test_case(&values, n_val);
        print_json(&nums, n);
    }
}