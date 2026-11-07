use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    k_val: i64,
) -> (result: (Vec<i32>, i64))
    requires
        1 <= fillers.len() <= 100_000,
        1 <= k_val <= 1_000_000_000_000_000,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1 <= 1_000_000_000_000_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
{
    let n: usize = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|j: int| 0 <= j < fillers.len() ==> 1 <= #[trigger] fillers[j] <= 100_000,
            forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 100_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }
    (nums, k_val)
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

fn make_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i64) {
    match mode {
        0 => {
            // tiny
            let n = rng.gen_range_usize(1, 5);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 10) as i32);
            }
            let k = rng.gen_range_i64(1, 100);
            (v, k)
        }
        1 => {
            // all ones, small k
            let n = rng.gen_range_usize(1, 100);
            let v = vec![1i32; n];
            let k = rng.gen_range_i64(1, 20);
            (v, k)
        }
        2 => {
            // all max values
            let n = rng.gen_range_usize(1, 1000);
            let v = vec![100_000i32; n];
            let k = rng.gen_range_i64(1, 1_000_000_000_000_000);
            (v, k)
        }
        3 => {
            // single element
            let val = rng.gen_range_i64(1, 100_000) as i32;
            (vec![val], rng.gen_range_i64(1, 1_000_000_000_000_000))
        }
        4 => {
            // k = 1, no subarrays valid
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 100_000) as i32);
            }
            (v, 1)
        }
        5 => {
            // k huge, all valid
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 100_000) as i32);
            }
            (v, 1_000_000_000_000_000)
        }
        6 => {
            // max size
            let n = 100_000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 100_000) as i32);
            }
            let k = rng.gen_range_i64(1, 1_000_000_000_000_000);
            (v, k)
        }
        7 => {
            // max size, all ones
            let n = 100_000usize;
            let v = vec![1i32; n];
            let k = rng.gen_range_i64(1, 1_000_000_000);
            (v, k)
        }
        8 => {
            // boundary k near sum*len
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            let mut total: i64 = 0;
            for _ in 0..n {
                let x = rng.gen_range_i64(1, 100);
                v.push(x as i32);
                total += x;
            }
            let score = total * (n as i64);
            let k = if score > 0 { score } else { 1 };
            (v, k)
        }
        9 => {
            // increasing
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(((i % 100_000) + 1) as i32);
            }
            let k = rng.gen_range_i64(1, 1_000_000_000_000);
            (v, k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 100_000) as i32);
            }
            let k = rng.gen_range_i64(1, 1_000_000_000_000_000);
            (v, k)
        }
    }
}

fn print_json(nums: &[i32], k: i64) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (fillers, k) = make_case(&mut rng, mode);
        let (nums, kk) = generate_test_case(&fillers, k);
        print_json(&nums, kk);
    }
}