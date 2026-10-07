use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    k_val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= fillers.len() <= 100_000,
        0 <= k_val <= 1_000_000_000,
        forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 1_000_000_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] <= 1_000_000_000,
            forall|j: int| 0 <= j < i as int ==> nums[j] == fillers[j],
            forall|j: int| 0 <= j < fillers.len() ==> 0 <= #[trigger] fillers[j] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i += 1;
    }
    (nums, k_val)
}

}

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

fn build_fillers(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(0);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(1_000_000_000);
            }
        }
        3 => {
            // decreasing: first is largest
            for i in 0..n {
                v.push((1_000_000_000 - (i as i32).min(1_000_000_000)).max(0));
            }
        }
        4 => {
            // increasing: last is largest
            for i in 0..n {
                v.push((i as i32).min(1_000_000_000));
            }
        }
        5 => {
            // zero prefix, then big
            for i in 0..n {
                if i < n / 2 {
                    v.push(0);
                } else {
                    v.push(1_000_000_000);
                }
            }
        }
        6 => {
            // big prefix, then zero
            for i in 0..n {
                if i < n / 2 {
                    v.push(1_000_000_000);
                } else {
                    v.push(0);
                }
            }
        }
        7 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
        }
        8 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { 0 } else { 1_000_000_000 });
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
        }
    }
    v
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
    let total = 220usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 13 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 10,
            4 => 100,
            5 => 1000,
            6 => 100_000,
            7 => rng.gen_range_usize(1, 50),
            8 => rng.gen_range_usize(1, 500),
            9 => rng.gen_range_usize(1, 5000),
            10 => 5,
            11 => 50,
            _ => rng.gen_range_usize(1, 100),
        };

        let fillers = build_fillers(&mut rng, n, mode);

        // Pick k with various adversarial choices
        let k: i32 = match t % 9 {
            0 => 0,
            1 => 1,
            2 => if n > i32::MAX as usize { 1_000_000_000 } else { n as i32 },
            3 => {
                let nv = n as i64;
                let v = (nv - 1).max(0);
                v as i32
            }
            4 => {
                let nv = n as i64;
                (nv + 1).min(1_000_000_000) as i32
            }
            5 => 1_000_000_000,
            6 => rng.gen_range_i32(0, 10),
            7 => rng.gen_range_i32(0, 1_000_000_000),
            _ => {
                let nv = n as i64;
                let lo = (nv - 2).max(0) as i32;
                let hi = ((nv + 2).min(1_000_000_000)) as i32;
                rng.gen_range_i32(lo, hi)
            }
        };

        let (nums, kk) = generate_test_case(&fillers, k);
        print_json(&nums, kk);
    }
}