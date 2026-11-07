use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
        1 <= k,
        k as int <= values.len() as int / 2,
    ensures
        2 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1,
        result.1 as int <= result.0.len() as int / 2,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |j: int| 0 <= j < i as int ==> #[trigger] nums[j] == values[j],
            forall |j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1000,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    assert(nums.len() == values.len());
    assert forall |j: int| 0 <= j < nums.len() implies 1 <= #[trigger] nums[j] <= 1000 by {
        assert(nums[j] == values[j]);
    }
    (nums, k)
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

fn clamp_val(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 1000 { 1000 } else { v }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all equal
            let x = rng.gen_range_i32(1, 1000);
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // strictly increasing
            let start = rng.gen_range_i32(1, 1000 - n as i32);
            for i in 0..n { v.push(clamp_val(start + i as i32)); }
        }
        2 => {
            // strictly decreasing
            let start = rng.gen_range_i32(n as i32, 1000);
            for i in 0..n { v.push(clamp_val(start - i as i32)); }
        }
        3 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        4 => {
            // all 1000
            for _ in 0..n { v.push(1000); }
        }
        5 => {
            // alternating high/low
            for i in 0..n {
                if i % 2 == 0 { v.push(1000); } else { v.push(1); }
            }
        }
        6 => {
            // random small range
            for _ in 0..n { v.push(rng.gen_range_i32(1, 5)); }
        }
        7 => {
            // random full range
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
        }
        8 => {
            // single peak
            let peak = rng.gen_range_usize(0, n - 1);
            for i in 0..n {
                if i == peak { v.push(1000); } else { v.push(rng.gen_range_i32(1, 999)); }
            }
        }
        9 => {
            // plateau with one bigger
            let base = rng.gen_range_i32(1, 999);
            for _ in 0..n { v.push(base); }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = clamp_val(base + 1);
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
        }
    }
    while v.len() < n { v.push(1); }
    v.truncate(n);
    v
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
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
        // n in [2, 100]
        let n = match t % 7 {
            0 => 2,
            1 => 3,
            2 => 4,
            3 => 100,
            4 => 99,
            5 => rng.gen_range_usize(2, 100),
            _ => rng.gen_range_usize(5, 50),
        };
        let max_k = (n / 2) as i32;
        let k = if max_k < 1 { 1 } else { rng.gen_range_i32(1, max_k) };
        let values = build_values(&mut rng, mode, n);
        // Safety: ensure values all in [1,1000]
        let values: Vec<i32> = values.into_iter().map(clamp_val).collect();
        let (nums, kk) = generate_test_case(&values, k);
        print_json(&nums, kk);
    }
}