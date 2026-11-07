use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
    limit: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 100_000,
        0 <= limit <= 1_000_000_000,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 1_000_000_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        result.1 == limit,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
        decreases n - i,
    {
        let v = vals[i];
        assert(1 <= v <= 1_000_000_000);
        nums.push(v);
        i = i + 1;
    }
    (nums, limit)
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vals(mode: usize, n: usize, rng: &mut Rng) -> (Vec<i32>, i32) {
    let mut vals: Vec<i32> = Vec::with_capacity(n);
    let limit: i32;
    match mode {
        0 => {
            // all same value
            let v = rng.gen_range_i32(1, 1_000_000_000);
            for _ in 0..n { vals.push(v); }
            limit = rng.gen_range_i32(0, 1_000_000_000);
        }
        1 => {
            // all 1s, limit 0
            for _ in 0..n { vals.push(1); }
            limit = 0;
        }
        2 => {
            // increasing sequence 1..n
            for i in 0..n { vals.push((i as i32 % 1_000_000_000) + 1); }
            limit = rng.gen_range_i32(0, 100);
        }
        3 => {
            // alternating min/max
            for i in 0..n {
                if i % 2 == 0 { vals.push(1); } else { vals.push(1_000_000_000); }
            }
            limit = rng.gen_range_i32(0, 1_000_000_000);
        }
        4 => {
            // random small
            for _ in 0..n { vals.push(rng.gen_range_i32(1, 10)); }
            limit = rng.gen_range_i32(0, 5);
        }
        5 => {
            // random large
            for _ in 0..n { vals.push(rng.gen_range_i32(1, 1_000_000_000)); }
            limit = rng.gen_range_i32(0, 1_000_000_000);
        }
        6 => {
            // Example 1: [8,2,4,7], limit=4
            let sample: [i32; 4] = [8, 2, 4, 7];
            for i in 0..n { vals.push(sample[i % 4]); }
            limit = 4;
        }
        7 => {
            // Example 2
            let sample: [i32; 6] = [10, 1, 2, 4, 7, 2];
            for i in 0..n { vals.push(sample[i % 6]); }
            limit = 5;
        }
        8 => {
            // Example 3
            let sample: [i32; 8] = [4, 2, 2, 2, 4, 4, 2, 2];
            for i in 0..n { vals.push(sample[i % 8]); }
            limit = 0;
        }
        9 => {
            // limit = max (full array valid)
            for _ in 0..n { vals.push(rng.gen_range_i32(1, 1_000_000_000)); }
            limit = 1_000_000_000;
        }
        _ => {
            // clustered: long runs then spike
            let base = rng.gen_range_i32(1, 500_000_000);
            for i in 0..n {
                if i % 10 == 9 { vals.push(1_000_000_000); }
                else { vals.push(base + (i as i32 % 50)); }
            }
            limit = rng.gen_range_i32(0, 100);
        }
    }
    (vals, limit)
}

fn print_json(nums: &[i32], limit: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"limit\":{}}}", limit);
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
            0 => 1 + (t % 10),
            1 => 100_000,
            2 => 1000,
            3 => if t % 2 == 0 { 2 } else { 500 },
            4 => 1 + (t % 50),
            5 => 100 + (t % 400),
            6 => 4 + (t % 20),
            7 => 6 + (t % 30),
            8 => 8 + (t % 40),
            9 => 1 + (t % 100),
            _ => 1000 + (t % 500),
        };
        let n = if n < 1 { 1 } else if n > 100_000 { 100_000 } else { n };

        let (vals, limit) = build_vals(mode, n, &mut rng);
        let (nums, lim) = generate_test_case(&vals, limit);
        print_json(&nums, lim);
    }
}