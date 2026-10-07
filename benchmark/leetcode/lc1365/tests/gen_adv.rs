use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 500,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100,
    ensures
        2 <= nums.len() <= 500,
        nums.len() == values.len(),
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            2 <= n <= 500,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    nums
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 2,
        1 => 500,
        2 => 2 + (t % 10),
        3 => 3 + (t % 20),
        4 => 100,
        5 => 250,
        6 => 499,
        7 => 50 + (t % 50),
        8 => 500,
        9 => 10 + (t % 30),
        _ => 2 + (t % 499),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);

    match mode {
        0 => {
            // smallest, random
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
        }
        1 => {
            // max size, random
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
        }
        2 => {
            // all same
            let x = rng.gen_range_i32(0, 100);
            for _ in 0..n {
                v.push(x);
            }
        }
        3 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        4 => {
            // all hundreds
            for _ in 0..n {
                v.push(100);
            }
        }
        5 => {
            // sorted ascending
            for i in 0..n {
                v.push(((i as i32) % 101).min(100));
            }
        }
        6 => {
            // sorted descending
            for i in 0..n {
                v.push((100 - ((i as i32) % 101)).max(0));
            }
        }
        7 => {
            // only 0 and 100
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(100);
                }
            }
        }
        8 => {
            // only small values (0-5)
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 5));
            }
        }
        9 => {
            // two distinct values
            let a = rng.gen_range_i32(0, 100);
            let b = rng.gen_range_i32(0, 100);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(a);
                } else {
                    v.push(b);
                }
            }
        }
        _ => {
            // random
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
        }
    }

    v
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
        let values = build_values(&mut rng, mode, t);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}