use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    k: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= fillers.len() <= 10_000,
        0 <= k <= 10_000,
        forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 10_000,
    ensures
        1 <= res.0.len() <= 10_000,
        forall|i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 10_000,
        0 <= res.1 <= 10_000,
        res.1 == k,
{
    let n: usize = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|j: int| 0 <= j < fillers.len() ==> 0 <= #[trigger] fillers[j] <= 10_000,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] <= 10_000,
            forall|j: int| 0 <= j < i as int ==> nums[j] == fillers[j],
        decreases n - i,
    {
        nums.push(fillers[i]);
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
        Self { state: seed }
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

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // Single element
            let v = rng.gen_range_i32(0, 10_000);
            let k = rng.gen_range_i32(0, 10_000);
            (vec![v], k)
        }
        1 => {
            // k = 0
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10_000));
            }
            (v, 0)
        }
        2 => {
            // k very large, diff <= 2k -> 0
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10_000));
            }
            (v, 10_000)
        }
        3 => {
            // All same
            let n = rng.gen_range_usize(1, 100);
            let val = rng.gen_range_i32(0, 10_000);
            let k = rng.gen_range_i32(0, 10_000);
            (vec![val; n], k)
        }
        4 => {
            // Min and max at extremes
            let n = rng.gen_range_usize(2, 50);
            let mut v = vec![5_000i32; n];
            v[0] = 0;
            v[n - 1] = 10_000;
            let k = rng.gen_range_i32(0, 10_000);
            (v, k)
        }
        5 => {
            // Two elements
            let a = rng.gen_range_i32(0, 10_000);
            let b = rng.gen_range_i32(0, 10_000);
            let k = rng.gen_range_i32(0, 10_000);
            (vec![a, b], k)
        }
        6 => {
            // Max length
            let mut v = Vec::with_capacity(10_000);
            for _ in 0..10_000 {
                v.push(rng.gen_range_i32(0, 10_000));
            }
            let k = rng.gen_range_i32(0, 10_000);
            (v, k)
        }
        7 => {
            // diff exactly 2k
            let k = rng.gen_range_i32(0, 5_000);
            let lo = rng.gen_range_i32(0, 10_000 - 2 * k);
            let hi = lo + 2 * k;
            let n = rng.gen_range_usize(2, 50);
            let mut v = vec![lo; n];
            v[n - 1] = hi;
            (v, k)
        }
        8 => {
            // diff = 2k + 1
            let k = rng.gen_range_i32(0, 4_999);
            let lo = rng.gen_range_i32(0, 10_000 - 2 * k - 1);
            let hi = lo + 2 * k + 1;
            let n = rng.gen_range_usize(2, 50);
            let mut v = vec![lo; n];
            v[n / 2] = hi;
            (v, k)
        }
        9 => {
            // Boundary: 0s and 10000s
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(10_000);
                }
            }
            (v, rng.gen_range_i32(0, 10_000))
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10_000));
            }
            let k = rng.gen_range_i32(0, 10_000);
            let _ = t;
            (v, k)
        }
    }
}

fn print_json(nums: &[i32], k: i32) {
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
        let (fillers, k) = build_case(&mut rng, mode, t);
        let (nums, k2) = generate_test_case(&fillers, k);
        print_json(&nums, k2);
    }
}