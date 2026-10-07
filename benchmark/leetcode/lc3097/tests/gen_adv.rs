use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 200000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
        0 <= k <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 200000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
        0 <= result.1 <= 1_000_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |j: int| 0 <= j < values.len() ==> 0 <= #[trigger] values[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < i as int ==> #[trigger] nums[j] == values[j],
            forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, i32) {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // random small values
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
            let k = rng.gen_range_i32(0, 200);
            (v, k)
        }
        1 => {
            // all zeros
            for _ in 0..n { v.push(0); }
            let k = rng.gen_range_i32(0, 10);
            (v, k)
        }
        2 => {
            // all max
            for _ in 0..n { v.push(1_000_000_000); }
            let k = rng.gen_range_i32(0, 1_000_000_000);
            (v, k)
        }
        3 => {
            // k = 0 (answer is 1)
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000_000));
            }
            (v, 0)
        }
        4 => {
            // k impossible (OR of all < k) — use small values and big k
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 3));
            }
            (v, 1_000_000_000)
        }
        5 => {
            // powers of 2
            for i in 0..n {
                let bit = (i % 30) as u32;
                v.push(1i32 << bit);
            }
            let k = rng.gen_range_i32(0, 1_000_000_000);
            (v, k)
        }
        6 => {
            // last element alone satisfies
            for _ in 0..(n-1) {
                v.push(rng.gen_range_i32(0, 5));
            }
            v.push(1_000_000_000);
            (v, 1_000_000_000)
        }
        7 => {
            // only full array satisfies
            // bits need to be combined
            for i in 0..n {
                let bit = (i % 30) as u32;
                v.push(1i32 << bit);
            }
            // k is OR of all small bits
            let mut k: i32 = 0;
            for i in 0..n {
                let bit = (i % 30) as u32;
                k |= 1i32 << bit;
            }
            (v, k)
        }
        8 => {
            // random medium
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            let k = rng.gen_range_i32(0, 1_000_000_000);
            (v, k)
        }
        9 => {
            // single element
            v.push(rng.gen_range_i32(0, 1_000_000_000));
            let k = rng.gen_range_i32(0, 1_000_000_000);
            (v, k)
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000_000));
            }
            let k = rng.gen_range_i32(0, 1_000_000_000);
            (v, k)
        }
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 50),
            1 => rng.gen_range_usize(1, 100),
            2 => rng.gen_range_usize(1, 100),
            3 => rng.gen_range_usize(1, 200),
            4 => rng.gen_range_usize(1, 200),
            5 => rng.gen_range_usize(2, 60),
            6 => rng.gen_range_usize(2, 100),
            7 => rng.gen_range_usize(2, 30),
            8 => rng.gen_range_usize(1, 1000),
            9 => 1,
            _ => rng.gen_range_usize(1, 500),
        };
        let n = if n < 1 { 1 } else if n > 200000 { 200000 } else { n };

        let (values, k) = build_values(&mut rng, mode, n);
        let (nums, k2) = generate_test_case(&values, k);
        print_json(&nums, k2);
    }
}