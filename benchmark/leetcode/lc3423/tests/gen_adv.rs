use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> -100 <= #[trigger] values[i] <= 100,
    ensures
        2 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            2 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -100 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> -100 <= #[trigger] nums[k] <= 100,
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

fn build_vec(vals: Vec<i32>) -> Vec<i32> {
    vals.into_iter().map(|v| v.clamp(-100, 100)).collect()
}

fn generate_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // minimum size n=2
            let a = rng.gen_range_i32(-100, 100);
            let b = rng.gen_range_i32(-100, 100);
            vec![a, b]
        }
        1 => {
            // maximum size n=100, random
            let n = 100;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
            v
        }
        2 => {
            // all same
            let x = rng.gen_range_i32(-100, 100);
            let n = rng.gen_range_usize(2, 100);
            vec![x; n]
        }
        3 => {
            // extremes: -100 and 100 alternating
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { -100 } else { 100 });
            }
            v
        }
        4 => {
            // sorted ascending
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            let start = rng.gen_range_i32(-100, 50);
            for i in 0..n {
                let val = (start as i64 + i as i64).min(100).max(-100) as i32;
                v.push(val);
            }
            v
        }
        5 => {
            // sorted descending - max diff should be in wrap
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            let start = rng.gen_range_i32(-50, 100);
            for i in 0..n {
                let val = (start as i64 - i as i64).min(100).max(-100) as i32;
                v.push(val);
            }
            v
        }
        6 => {
            // extremes at first and last only
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            v.push(-100);
            for _ in 1..n-1 {
                v.push(0);
            }
            if n >= 2 {
                v.push(100);
            }
            v
        }
        7 => {
            // big jump somewhere in middle
            let n = rng.gen_range_usize(4, 100);
            let mut v = Vec::with_capacity(n);
            let mid = n / 2;
            for i in 0..n {
                if i == mid {
                    v.push(100);
                } else if i == mid - 1 {
                    v.push(-100);
                } else {
                    v.push(0);
                }
            }
            v
        }
        8 => {
            // n=2 with extremes
            vec![-100, 100]
        }
        9 => {
            // n=3 spec example variations
            let a = rng.gen_range_i32(-100, 100);
            let b = rng.gen_range_i32(-100, 100);
            let c = rng.gen_range_i32(-100, 100);
            vec![a, b, c]
        }
        _ => {
            // all zeros
            let n = rng.gen_range_usize(2, 100);
            vec![0; n]
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("]}}");
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
        let raw = generate_mode(&mut rng, mode);
        let clamped = build_vec(raw);
        let v = if clamped.len() < 2 {
            vec![0, 0]
        } else if clamped.len() > 100 {
            clamped[..100].to_vec()
        } else {
            clamped
        };
        let nums = generate_test_case(&v);
        print_json(&nums);
    }
}