use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i32,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        3 <= n <= 100_000,
        1 <= k as int <= n as int / 2,
        fillers.len() == n,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1_000_000,
    ensures
        3 <= result.0.len() <= 100_000,
        result.0.len() == n,
        result.1 == k,
        1 <= result.1 as int <= result.0.len() as int / 2,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            fillers.len() == n,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 1_000_000,
            forall |j: int| 0 <= j < fillers.len() ==> 1 <= #[trigger] fillers[j] <= 1_000_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i += 1;
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn clamp_val(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 1_000_000 { 1_000_000 } else { v }
}

fn build_fillers(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all equal
            let x = rng.gen_range_i32(1, 1_000_000);
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // strictly increasing
            let start = rng.gen_range_i32(1, 100);
            for i in 0..n {
                v.push(clamp_val(start + i as i32));
            }
        }
        2 => {
            // strictly decreasing
            let start = rng.gen_range_i32(1, 1_000_000);
            for i in 0..n {
                v.push(clamp_val(start - i as i32));
            }
        }
        3 => {
            // random small range 1..3
            for _ in 0..n { v.push(rng.gen_range_i32(1, 3)); }
        }
        4 => {
            // random large range
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1_000_000)); }
        }
        5 => {
            // valley pattern: decreasing then increasing
            let mid = n / 2;
            for i in 0..n {
                let d = if i <= mid { mid - i } else { i - mid };
                v.push(clamp_val(1 + d as i32));
            }
        }
        6 => {
            // mountain pattern
            let mid = n / 2;
            for i in 0..n {
                let d = if i <= mid { i } else { n - i };
                v.push(clamp_val(1 + d as i32));
            }
        }
        7 => {
            // alternating
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 1_000_000 });
            }
        }
        8 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        9 => {
            // all max
            for _ in 0..n { v.push(1_000_000); }
        }
        _ => {
            // plateaus
            let block = (rng.gen_range_usize(1, 5)).max(1);
            let mut cur = rng.gen_range_i32(1, 100);
            for i in 0..n {
                if i > 0 && i % block == 0 {
                    cur = rng.gen_range_i32(1, 1_000_000);
                }
                v.push(cur);
            }
        }
    }
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match t % 7 {
            0 => 3,
            1 => 4,
            2 => rng.gen_range_usize(5, 20),
            3 => rng.gen_range_usize(20, 100),
            4 => rng.gen_range_usize(100, 1000),
            5 => 100_000,
            _ => rng.gen_range_usize(3, 500),
        };

        // k in [1, n/2]
        let kmax = (n / 2) as i32;
        let k = if kmax < 1 { 1 } else { rng.gen_range_i32(1, kmax) };

        let fillers = build_fillers(&mut rng, n, mode);

        // Safety: ensure all in range
        let mut fillers = fillers;
        for i in 0..fillers.len() {
            fillers[i] = clamp_val(fillers[i]);
        }

        let (nums, kk) = generate_test_case(n, k, &fillers);
        print_json(&nums, kk);
    }
}