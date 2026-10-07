use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
    k: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 100_000,
        1 <= k <= vals.len(),
        forall |i: int| 0 <= i < vals.len() ==> -10_000 <= #[trigger] vals@[i] <= 10_000,
    ensures
        result.0.len() == vals.len(),
        result.1 == k,
        result.0.len() <= 100_000,
        1 <= result.1 <= result.0.len(),
        forall |i: int| 0 <= i < result.0.len() ==> -10_000 <= #[trigger] result.0@[i] <= 10_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |j: int| 0 <= j < i as int ==> -10_000 <= #[trigger] nums@[j] <= 10_000,
            forall |j: int| 0 <= j < vals.len() ==> -10_000 <= #[trigger] vals@[j] <= 10_000,
        decreases n - i,
    {
        nums.push(vals[i]);
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vals(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_i32(-10_000, 10_000));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(10_000);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(-10_000);
            }
        }
        3 => {
            for _ in 0..n {
                v.push(0);
            }
        }
        4 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { 10_000 } else { -10_000 });
            }
        }
        5 => {
            for i in 0..n {
                v.push(if i < n / 2 { -10_000 } else { 10_000 });
            }
        }
        6 => {
            for i in 0..n {
                v.push(if i < n / 2 { 10_000 } else { -10_000 });
            }
        }
        7 => {
            for _ in 0..n {
                v.push(rng.gen_i32(-5, 5));
            }
        }
        8 => {
            let spike = rng.gen_usize(0, n - 1);
            for i in 0..n {
                v.push(if i == spike { 10_000 } else { -10_000 });
            }
        }
        9 => {
            for i in 0..n {
                let sign = if rng.next_u64() % 2 == 0 { 1 } else { -1 };
                let _ = i;
                v.push(sign * 10_000);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_i32(-100, 100));
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match t % 13 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 10,
            4 => 100,
            5 => 1000,
            6 => 100_000,
            7 => 50_000,
            8 => rng.gen_usize(1, 500),
            9 => rng.gen_usize(1, 50),
            10 => 99_999,
            11 => rng.gen_usize(1, 10),
            _ => rng.gen_usize(1, 2000),
        };

        let k: i32 = match t % 5 {
            0 => 1,
            1 => n as i32,
            2 => ((n + 1) / 2) as i32,
            3 => rng.gen_usize(1, n) as i32,
            _ => if n >= 4 { (n / 4 + 1) as i32 } else { 1 },
        };

        let vals = build_vals(&mut rng, mode, n);
        let (nums, k_out) = generate_test_case(&vals, k);
        print_json(&nums, k_out);
    }
}