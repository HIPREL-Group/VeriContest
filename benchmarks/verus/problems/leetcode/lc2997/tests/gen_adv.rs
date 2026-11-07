use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    k: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= fillers.len() <= 100_000,
        0 <= k <= 1_000_000,
        forall |i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 1_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 1_000_000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < fillers.len()
        invariant
            0 <= i <= fillers.len(),
            nums.len() == i,
            forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] <= 1_000_000,
            forall |j: int| 0 <= j < fillers.len() ==> 0 <= #[trigger] fillers[j] <= 1_000_000,
        decreases fillers.len() - i,
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
        self.state = self
            .state
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

fn build_vec(values: Vec<i32>, k: i32) -> (Vec<i32>, i32) {
    // Clamp values into [0, 1_000_000]
    let clamped: Vec<i32> = values
        .into_iter()
        .map(|v| {
            let mut x = v;
            if x < 0 {
                x = -x;
            }
            if x > 1_000_000 {
                x = x % 1_000_001;
            }
            if x < 0 {
                x = 0;
            }
            x
        })
        .collect();
    let kk = if k < 0 {
        -k
    } else if k > 1_000_000 {
        k % 1_000_001
    } else {
        k
    };
    let kk = if kk < 0 { 0 } else { kk };
    generate_test_case(&clamped, kk)
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

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // Small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 20));
            }
            let k = rng.gen_range_i32(0, 20);
            (v, k)
        }
        1 => {
            // Single element
            let v = vec![rng.gen_range_i32(0, 1_000_000)];
            let k = rng.gen_range_i32(0, 1_000_000);
            (v, k)
        }
        2 => {
            // All zeros
            let n = rng.gen_range_usize(1, 100);
            let v = vec![0i32; n];
            let k = rng.gen_range_i32(0, 1_000_000);
            (v, k)
        }
        3 => {
            // k = 0
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            (v, 0)
        }
        4 => {
            // XOR equals k already
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            let mut xor_so_far: i32 = 0;
            for _ in 0..n - 1 {
                let x = rng.gen_range_i32(0, 1_000_000);
                v.push(x);
                xor_so_far ^= x;
            }
            let k = rng.gen_range_i32(0, 1_000_000);
            // last element makes xor = k
            let last = xor_so_far ^ k;
            let last = if last < 0 || last > 1_000_000 {
                rng.gen_range_i32(0, 1_000_000)
            } else {
                last
            };
            v.push(last);
            (v, k)
        }
        5 => {
            // Max values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(1_000_000);
            }
            (v, 1_000_000)
        }
        6 => {
            // Large n
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            let k = rng.gen_range_i32(0, 1_000_000);
            (v, k)
        }
        7 => {
            // Powers of two
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::new();
            for _ in 0..n {
                let bit = rng.gen_range_usize(0, 19);
                v.push(1i32 << bit);
            }
            let k = 1i32 << rng.gen_range_usize(0, 19);
            (v, k)
        }
        8 => {
            // k is max, nums small
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
            (v, 1_000_000)
        }
        9 => {
            // All same
            let n = rng.gen_range_usize(1, 100);
            let val = rng.gen_range_i32(0, 1_000_000);
            let v = vec![val; n];
            let k = rng.gen_range_i32(0, 1_000_000);
            (v, k)
        }
        _ => {
            // Default random
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            let k = rng.gen_range_i32(0, 1_000_000);
            (v, k)
        }
    }
    .clone()
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
        let (v, k) = gen_mode(&mut rng, mode, t);
        let (nums, kk) = build_vec(v, k);
        print_json(&nums, kk);
    }
}