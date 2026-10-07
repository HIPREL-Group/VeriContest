use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 10_000,
        forall|i: int| 0 <= i < values.len() ==> -1_000_000_000 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 10_000,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> -1_000_000_000 <= #[trigger] values[k] <= 1_000_000_000,
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Single element
            vec![rng.gen_range_i32(-1_000_000_000, 1_000_000_000)]
        }
        1 => {
            // All equal
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            vec![v; n]
        }
        2 => {
            // Strictly increasing all the way
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            let mut cur: i32 = -500_000;
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_add(1);
            }
            v
        }
        3 => {
            // Strictly decreasing
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            let mut cur: i32 = 500_000;
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_sub(1);
            }
            v
        }
        4 => {
            // Random small
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10, 10));
            }
            v
        }
        5 => {
            // Random large
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
            v
        }
        6 => {
            // Max size strictly increasing
            let n = 10_000usize;
            let mut v = Vec::with_capacity(n);
            let mut cur: i32 = -1_000_000_000;
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_add(1);
            }
            v
        }
        7 => {
            // Max size all equal
            vec![0i32; 10_000]
        }
        8 => {
            // Max size random
            let n = 10_000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
            v
        }
        9 => {
            // Sawtooth pattern: increasing blocks
            let block = rng.gen_range_usize(1, 10);
            let blocks = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for _b in 0..blocks {
                let start = rng.gen_range_i32(-100, 100);
                for k in 0..block {
                    v.push(start + k as i32);
                }
            }
            if v.is_empty() { v.push(0); }
            if v.len() > 10_000 { v.truncate(10_000); }
            v
        }
        10 => {
            // Boundary values
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for i in 0..n {
                if (i + t) % 2 == 0 {
                    v.push(1_000_000_000);
                } else {
                    v.push(-1_000_000_000);
                }
            }
            v
        }
        _ => {
            // Plateau with one increase
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![5i32; n];
            let pos = rng.gen_range_usize(0, n - 1);
            v[pos] = 10;
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 12usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode, t);
        // Clamp size to [1, 10000]
        let mut values = values;
        if values.is_empty() { values.push(0); }
        if values.len() > 10_000 { values.truncate(10_000); }
        // Clamp values to range
        for v in values.iter_mut() {
            if *v < -1_000_000_000 { *v = -1_000_000_000; }
            if *v > 1_000_000_000 { *v = 1_000_000_000; }
        }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}