use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    nums
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

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 100,
        2 => 2,
        3 => rng.gen_range_usize(1, 100),
        4 => rng.gen_range_usize(1, 100),
        5 => rng.gen_range_usize(1, 100),
        6 => 50,
        7 => 100,
        8 => rng.gen_range_usize(1, 10),
        9 => 100,
        _ => rng.gen_range_usize(1, 100),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // single element
            v.push(rng.gen_range_i32(1, 1000));
        }
        1 => {
            // all max values
            for _ in 0..n {
                v.push(1000);
            }
        }
        2 => {
            // all ones
            for _ in 0..n {
                v.push(1);
            }
        }
        3 => {
            // values <= 1 (so start = i - 1 or 0)
            for _ in 0..n {
                v.push(1);
            }
        }
        4 => {
            // nums[i] very large, forcing start=0 often
            for _ in 0..n {
                v.push(rng.gen_range_i32(500, 1000));
            }
        }
        5 => {
            // nums[i] == i (each looks at own index back)
            for i in 0..n {
                let val = ((i + 1) as i32).min(1000).max(1);
                v.push(val);
            }
        }
        6 => {
            // alternating small/large
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(1);
                } else {
                    v.push(1000);
                }
            }
        }
        7 => {
            // decreasing
            for i in 0..n {
                let val = (1000 - (i as i32) * 10).max(1);
                v.push(val);
            }
        }
        8 => {
            // small random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 5));
            }
        }
        9 => {
            // values exactly equal to index+1 clamped
            for i in 0..n {
                let val = (((i as i32) % 1000) + 1).max(1).min(1000);
                v.push(val);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
    }
    let _ = t;
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
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
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_values(&mut rng, mode, t);
        // Safety: build_values always produces 1..=100 values in [1,1000]
        let clipped: Vec<i32> = values.into_iter()
            .take(100)
            .map(|x| if x < 1 { 1 } else if x > 1000 { 1000 } else { x })
            .collect();
        let safe = if clipped.is_empty() { vec![1i32] } else { clipped };
        let nums = generate_test_case(&safe);
        print_json(&nums);
    }
}