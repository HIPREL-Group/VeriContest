use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
        1 <= k <= values.len(),
    ensures
        1 <= res.0.len() <= 100,
        forall|i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 100,
        1 <= res.1 <= res.0.len(),
        res.1 == k,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 100,
            forall|j: int| 0 <= j < i as int ==> nums[j] == values[j],
            forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 100,
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // minimum size n=1
            let v = rng.gen_range_i32(1, 100);
            (vec![v], 1)
        }
        1 => {
            // small n, k = n
            let n = rng.gen_range_usize(1, 5);
            let mut nums = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100));
            }
            (nums, n as i32)
        }
        2 => {
            // small n, k = 1
            let n = rng.gen_range_usize(1, 10);
            let mut nums = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100));
            }
            (nums, 1)
        }
        3 => {
            // max size 100
            let n = 100usize;
            let mut nums = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100));
            }
            let k = rng.gen_range_usize(1, 100);
            (nums, k as i32)
        }
        4 => {
            // all equal
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(1, 100);
            let nums = vec![v; n];
            let k = rng.gen_range_usize(1, n);
            (nums, k as i32)
        }
        5 => {
            // all 1s
            let n = rng.gen_range_usize(1, 100);
            let nums = vec![1i32; n];
            let k = rng.gen_range_usize(1, n);
            (nums, k as i32)
        }
        6 => {
            // all 100s
            let n = rng.gen_range_usize(1, 100);
            let nums = vec![100i32; n];
            let k = rng.gen_range_usize(1, n);
            (nums, k as i32)
        }
        7 => {
            // mix of 1 and 100
            let n = rng.gen_range_usize(2, 100);
            let mut nums = Vec::new();
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    nums.push(1);
                } else {
                    nums.push(100);
                }
            }
            let k = rng.gen_range_usize(1, n);
            (nums, k as i32)
        }
        8 => {
            // sorted ascending
            let n = rng.gen_range_usize(1, 100);
            let mut nums = Vec::new();
            for i in 0..n {
                let v = ((i % 100) + 1) as i32;
                nums.push(v);
            }
            let k = rng.gen_range_usize(1, n);
            (nums, k as i32)
        }
        9 => {
            // k = n/2
            let n = rng.gen_range_usize(2, 100);
            let mut nums = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100));
            }
            let k = (n / 2).max(1);
            (nums, k as i32)
        }
        _ => {
            // random
            let n = rng.gen_range_usize(1, 100);
            let mut nums = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100));
            }
            let k = rng.gen_range_usize(1, n);
            let _ = t;
            (nums, k as i32)
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
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (values, k) = build(&mut rng, mode, t);
        // Ensure constraints are met before calling verified generator
        if values.is_empty() || values.len() > 100 { continue; }
        if k < 1 || k as usize > values.len() { continue; }
        let mut ok = true;
        for &v in &values {
            if v < 1 || v > 100 { ok = false; break; }
        }
        if !ok { continue; }
        let (nums, kk) = generate_test_case(&values, k);
        print_json(&nums, kk);
    }
}