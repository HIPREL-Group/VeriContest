use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10_000,
        1 <= k,
        k as int <= values.len() as int,
    ensures
        1 <= res.0.len() <= 100_000,
        forall|i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 10_000,
        1 <= res.1,
        res.1 as int <= res.0.len() as int,
{
    let mut out: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            out.len() == i,
            forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] out[j] <= 10_000,
            forall|j: int| 0 <= j < i as int ==> out[j] == values[j],
            forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 10_000,
        decreases n - i,
    {
        out.push(values[i]);
        i += 1;
    }
    (out, k)
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(1, 10),
        3 => rng.gen_range_usize(50, 200),
        4 => 100_000,
        5 => 99_999,
        6 => rng.gen_range_usize(1000, 5000),
        7 => 1 + (t % 7),
        8 => rng.gen_range_usize(1, 100_000),
        9 => 1000,
        _ => rng.gen_range_usize(1, 1000),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 | 1 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10_000));
            }
        }
        3 => {
            // All same
            let x = rng.gen_range_i32(1, 10_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        4 | 5 => {
            // Large array random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10_000));
            }
        }
        6 => {
            // Sorted ascending-ish
            for i in 0..n {
                let base = 1 + (i as i32 % 10_000);
                v.push(base);
            }
        }
        7 => {
            // Max values
            for _ in 0..n {
                v.push(10_000);
            }
        }
        8 => {
            // Min values
            for _ in 0..n {
                v.push(1);
            }
        }
        9 => {
            // Half large, half small
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(10_000);
                } else {
                    v.push(1);
                }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10_000));
            }
        }
    }

    // Edge k values for some modes
    let k: i32 = match mode {
        0 => 1,
        1 => {
            // k = 1 or 2
            if t % 2 == 0 { 1 } else { 2 }
        }
        4 | 5 => rng.gen_range_i32(1, n as i32),
        7 => n as i32, // take all
        8 => 1,        // take one
        _ => {
            let kk = rng.gen_range_usize(1, n);
            kk as i32
        }
    };
    (v, k)
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"card_points\":[");
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
        let (values, k) = build(&mut rng, mode, t);
        let (cards, kk) = generate_test_case(&values, k);
        print_json(&cards, kk);
    }
}