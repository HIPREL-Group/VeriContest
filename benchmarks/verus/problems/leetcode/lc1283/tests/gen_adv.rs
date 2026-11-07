use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    threshold: i32,
    vals: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 50_000,
        vals.len() == n,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1_000_000,
        n <= threshold <= 1_000_000,
    ensures
        ({
            let nums = result.0;
            let thr = result.1;
            &&& 1 <= nums.len() <= 50_000
            &&& (forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000)
            &&& nums.len() <= thr <= 1_000_000
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            vals.len() == n,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 1_000_000,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000,
        decreases n - i,
    {
        nums.push(vals[i]);
        i = i + 1;
    }
    (nums, threshold)
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
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (usize, i32, Vec<i32>) {
    // returns (n, threshold, vals)
    let (n, max_val) = match mode {
        0 => (1usize, 1_000_000i32),
        1 => (2, 1_000_000),
        2 => (50_000, 1_000_000),
        3 => (50_000, 1),
        4 => (rng.gen_range_usize(1, 100), 1_000_000),
        5 => (rng.gen_range_usize(1, 100), 1),
        6 => (rng.gen_range_usize(1, 1000), rng.gen_range_i32(1, 1_000_000)),
        7 => (rng.gen_range_usize(100, 5000), rng.gen_range_i32(1, 100)),
        8 => (10, 1_000_000),
        9 => (1, 1),
        _ => (rng.gen_range_usize(1, 2000), rng.gen_range_i32(1, 1_000_000)),
    };

    let mut vals = Vec::with_capacity(n);
    for _ in 0..n {
        let v = match mode {
            2 => rng.gen_range_i32(1, 1_000_000),
            3 => 1,
            8 => if rng.next_u64() % 2 == 0 { 1 } else { 1_000_000 },
            _ => rng.gen_range_i32(1, max_val.max(1)),
        };
        vals.push(v);
    }

    // threshold in [n, 1_000_000]
    let n_i32 = n as i32;
    let threshold = if n_i32 >= 1_000_000 {
        1_000_000
    } else {
        let lo = n_i32;
        let hi = 1_000_000i32;
        // adversarial: sometimes pick exactly n, sometimes max, sometimes random
        match mode % 4 {
            0 => lo,
            1 => hi,
            2 => {
                if hi > lo { lo + (rng.next_u64() % (hi - lo + 1) as u64) as i32 } else { lo }
            }
            _ => {
                // midpoint
                lo + (hi - lo) / 2
            }
        }
    };

    (n, threshold, vals)
}

fn print_json(nums: &[i32], divisor: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"threshold\":{}}}", divisor);
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
        let (n, threshold, vals) = build_case(&mut rng, mode);
        let (nums, thr) = generate_test_case(n, threshold, &vals);
        print_json(&nums, thr);
    }
}