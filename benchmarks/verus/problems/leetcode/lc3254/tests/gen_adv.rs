use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k_val: usize,
    base: i32,
    break_positions: &Vec<bool>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 500,
        1 <= k_val <= n,
        1 <= base <= 50_000,
        break_positions.len() == n,
    ensures
        1 <= result.0.len() <= 500,
        1 <= result.1 <= result.0.len(),
        result.0.len() == n,
        result.1 == k_val as i32,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut cur: i32 = base;
    let mut i: usize = 0;
    while i < n
        invariant
            n <= 500,
            1 <= base <= 50_000,
            break_positions.len() == n,
            nums.len() == i,
            0 <= i <= n,
            1 <= cur <= 100_000,
            forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100_000,
        decreases n - i,
    {
        nums.push(cur);
        // Next value
        if i + 1 < n {
            if break_positions[i] {
                // jump to a different value
                if cur >= 50_000 {
                    cur = 1;
                } else {
                    cur = cur + 10_000;
                    if cur > 100_000 { cur = 1; }
                }
            } else {
                if cur >= 100_000 {
                    cur = 1;
                } else {
                    cur = cur + 1;
                }
            }
        }
        i = i + 1;
    }

    (nums, k_val as i32)
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
    fn gen_bool(&mut self, prob_num: u32, prob_den: u32) -> bool {
        (self.next_u64() as u32 % prob_den) < prob_num
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

fn build_and_print(rng: &mut Rng, n: usize, k: usize, base: i32, breaks: Vec<bool>) {
    let (nums, k_out) = generate_test_case(n, k, base, &breaks);
    let _ = rng;
    print_json(&nums, k_out);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;

    for t in 0..total {
        let mode = t % 10;
        let (n, k, base, breaks) = match mode {
            0 => {
                // small random
                let n = rng.gen_range_usize(1, 10);
                let k = rng.gen_range_usize(1, n);
                let base = rng.gen_range_usize(1, 50_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(rng.gen_bool(1, 3)); }
                (n, k, base, breaks)
            }
            1 => {
                // all consecutive
                let n = rng.gen_range_usize(5, 100);
                let k = rng.gen_range_usize(1, n);
                let base = rng.gen_range_usize(1, 40_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(false); }
                (n, k, base, breaks)
            }
            2 => {
                // k == 1
                let n = rng.gen_range_usize(1, 500);
                let k = 1usize;
                let base = rng.gen_range_usize(1, 50_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(rng.gen_bool(1, 2)); }
                (n, k, base, breaks)
            }
            3 => {
                // k == n
                let n = rng.gen_range_usize(1, 500);
                let k = n;
                let base = rng.gen_range_usize(1, 50_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(rng.gen_bool(1, 5)); }
                (n, k, base, breaks)
            }
            4 => {
                // maximum size
                let n = 500usize;
                let k = rng.gen_range_usize(1, 500);
                let base = rng.gen_range_usize(1, 50_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(rng.gen_bool(1, 10)); }
                (n, k, base, breaks)
            }
            5 => {
                // all breaks
                let n = rng.gen_range_usize(2, 50);
                let k = rng.gen_range_usize(1, n);
                let base = rng.gen_range_usize(1, 50_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(true); }
                (n, k, base, breaks)
            }
            6 => {
                // only break at position k-1
                let n = rng.gen_range_usize(3, 30);
                let k = rng.gen_range_usize(2, n);
                let base = rng.gen_range_usize(1, 50_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for i in 0..n {
                    breaks.push(i + 1 == k);
                }
                (n, k, base, breaks)
            }
            7 => {
                // small with k=2
                let n = rng.gen_range_usize(2, 20);
                let k = 2usize;
                let base = rng.gen_range_usize(1, 50_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(rng.gen_bool(1, 2)); }
                (n, k, base, breaks)
            }
            8 => {
                // base near max
                let n = rng.gen_range_usize(5, 100);
                let k = rng.gen_range_usize(1, n);
                let base = 40_000i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(rng.gen_bool(1, 4)); }
                (n, k, base, breaks)
            }
            _ => {
                // typical random
                let n = rng.gen_range_usize(1, 500);
                let k = rng.gen_range_usize(1, n);
                let base = rng.gen_range_usize(1, 50_000) as i32;
                let mut breaks = Vec::with_capacity(n);
                for _ in 0..n { breaks.push(rng.gen_bool(1, 4)); }
                (n, k, base, breaks)
            }
        };
        build_and_print(&mut rng, n, k, base, breaks);
    }
}