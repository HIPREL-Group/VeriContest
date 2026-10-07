use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    k_val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= fillers.len() <= 100_000,
        1 <= k_val <= 1_000_000_000,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        ({
            let nums = result.0;
            let k = result.1;
            &&& 1 <= nums.len() <= 100_000
            &&& forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000
            &&& 1 <= k <= 1_000_000_000
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == fillers.len(),
            nums.len() == i,
            forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 1_000_000_000,
            forall|j: int| 0 <= j < fillers.len() ==> 1 <= #[trigger] fillers[j] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }
    (nums, k_val)
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn make_random(rng: &mut Rng, n: usize, max_val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, max_val));
    }
    v
}

fn make_all_same(n: usize, val: i32) -> Vec<i32> {
    vec![val; n]
}

fn make_alternating(n: usize, a: i32, b: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 { v.push(a); } else { v.push(b); }
    }
    v
}

fn make_increasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push((i as i32) + 1);
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
    } else {
        1
    };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let (fillers, k_val): (Vec<i32>, i32) = match mode {
            0 => {
                // Small random
                let n = rng.gen_range_usize(1, 10);
                let k = rng.gen_range_i32(1, 20);
                (make_random(&mut rng, n, 10), k)
            }
            1 => {
                // Single element
                (vec![rng.gen_range_i32(1, 1_000_000_000)], rng.gen_range_i32(1, 1_000_000_000))
            }
            2 => {
                // All same, k = 2*val
                let val = rng.gen_range_i32(1, 500_000_000);
                let n = rng.gen_range_usize(2, 100);
                (make_all_same(n, val), val.saturating_mul(2).max(1))
            }
            3 => {
                // All same, k = 2*val - odd count
                let val = rng.gen_range_i32(1, 500_000_000);
                let n = 2 * rng.gen_range_usize(1, 50) + 1;
                (make_all_same(n, val), val.saturating_mul(2).max(1))
            }
            4 => {
                // Alternating a, b with a+b=k
                let a = rng.gen_range_i32(1, 999_999_999);
                let b = rng.gen_range_i32(1, 1_000_000_000 - a);
                let n = rng.gen_range_usize(2, 200);
                (make_alternating(n, a, b), a + b)
            }
            5 => {
                // Increasing 1..n
                let n = rng.gen_range_usize(2, 100);
                let k = rng.gen_range_i32(2, (n as i32) + 1);
                (make_increasing(n), k)
            }
            6 => {
                // Max values
                let n = rng.gen_range_usize(1, 50);
                (make_all_same(n, 1_000_000_000), 1_000_000_000)
            }
            7 => {
                // Large n
                let n = 100_000;
                let a = rng.gen_range_i32(1, 999_999_998);
                let k = a + a + 1;
                (make_alternating(n, a, a + 1), k)
            }
            8 => {
                // k=1 (no pairs possible since min 1+1=2)
                let n = rng.gen_range_usize(1, 50);
                (make_random(&mut rng, n, 1_000_000_000), 1)
            }
            _ => {
                // Random medium
                let n = rng.gen_range_usize(1, 1000);
                let k = rng.gen_range_i32(1, 1_000_000_000);
                (make_random(&mut rng, n, 1_000_000_000), k)
            }
        };

        // sanity-bound clamp to ensure within spec limits
        let mut safe_fillers = fillers;
        if safe_fillers.is_empty() {
            safe_fillers.push(1);
        }
        if safe_fillers.len() > 100_000 {
            safe_fillers.truncate(100_000);
        }
        for x in safe_fillers.iter_mut() {
            if *x < 1 { *x = 1; }
            if *x > 1_000_000_000 { *x = 1_000_000_000; }
        }
        let mut safe_k = k_val;
        if safe_k < 1 { safe_k = 1; }
        if safe_k > 1_000_000_000 { safe_k = 1_000_000_000; }

        let (nums, k) = generate_test_case(&safe_fillers, safe_k);
        print_json(&nums, k);
    }
}