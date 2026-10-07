use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    index_difference: i32,
    value_difference: i32,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= values.len() <= 100_000,
        0 <= index_difference <= 100_000,
        0 <= value_difference <= 1_000_000_000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 100_000,
        0 <= result.2 <= 1_000_000_000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == values.len(),
            nums.len() == k,
            forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < k as int ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < k as int ==> nums[i] == values[i],
        decreases n - k,
    {
        nums.push(values[k]);
        k = k + 1;
    }
    (nums, index_difference, value_difference)
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

fn build(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32, i32) {
    let (n, idx_diff, val_diff): (usize, i32, i32) = match mode {
        0 => (1, 0, 0),
        1 => (2, 0, 0),
        2 => (2, 1, 1_000_000_000),
        3 => (100_000, 100_000, 1_000_000_000),
        4 => (100_000, 0, 0),
        5 => (rng.gen_range_usize(1, 20), rng.gen_range_i32(0, 20), rng.gen_range_i32(0, 100)),
        6 => (rng.gen_range_usize(1, 1000), rng.gen_range_i32(0, 1000), rng.gen_range_i32(0, 1_000_000_000)),
        7 => (rng.gen_range_usize(50, 100), rng.gen_range_i32(0, 50), 0),
        8 => (10, 5, 500_000_000),
        9 => (100_000, 50_000, 500_000_000),
        _ => (rng.gen_range_usize(1, 500) + (t % 100), rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 1_000_000_000)),
    };

    let mut values: Vec<i32> = Vec::with_capacity(n);
    match mode {
        2 => {
            values.push(0);
            values.push(1_000_000_000);
        }
        4 => {
            for _ in 0..n { values.push(5); }
        }
        7 => {
            for i in 0..n {
                values.push(if i % 2 == 0 { 0 } else { 1_000_000_000 });
            }
        }
        8 => {
            for i in 0..n {
                values.push((i as i32) * 100_000_000);
            }
        }
        _ => {
            for _ in 0..n {
                values.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
    }
    (values, idx_diff, val_diff)
}

fn print_json(nums: &[i32], idx_diff: i32, val_diff: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"index_difference\":{},\"value_difference\":{}}}", idx_diff, val_diff);
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
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (values, idx_diff, val_diff) = build(&mut rng, mode, t);
        let (nums, id, vd) = generate_test_case(&values, idx_diff, val_diff);
        print_json(&nums, id, vd);
    }
}