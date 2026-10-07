use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (res: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= res.len() <= 100_000,
        forall |i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] <= 100_000,
{
    let mut result: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            result.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100_000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] result[k] <= 100_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] result[k] == values[k],
        decreases n - i,
    {
        result.push(values[i]);
        i += 1;
    }
    result
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
            v
        }
        1 => {
            // all same
            let n = rng.gen_range_usize(1, 1000);
            let val = rng.gen_range_i32(1, 100_000);
            vec![val; n]
        }
        2 => {
            // strictly increasing
            let n = rng.gen_range_usize(1, 1000);
            (1..=n as i32).collect()
        }
        3 => {
            // strictly decreasing
            let n = rng.gen_range_usize(1, 1000);
            (1..=n as i32).rev().collect()
        }
        4 => {
            // single element
            vec![rng.gen_range_i32(1, 100_000)]
        }
        5 => {
            // large random with small value range
            let n = rng.gen_range_usize(100, 5000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            v
        }
        6 => {
            // large random full range
            let n = rng.gen_range_usize(100, 5000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
            v
        }
        7 => {
            // max size stress (smaller because printing is expensive)
            let n = 10_000;
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
            v
        }
        8 => {
            // boundary values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                let pick = rng.next_u64() % 3;
                let val = match pick {
                    0 => 1,
                    1 => 100_000,
                    _ => rng.gen_range_i32(1, 100_000),
                };
                v.push(val);
            }
            v
        }
        9 => {
            // alternating big small
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 100_000 });
            }
            v
        }
        10 => {
            // zigzag
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for i in 0..n {
                let base = (i as i32 % 100) + 1;
                let val = if i % 2 == 0 { base } else { 101 - base };
                v.push(val.max(1));
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"instructions\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode);
        let out = generate_test_case(&values);
        print_json(&out);
    }
}