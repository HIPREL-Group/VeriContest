use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 1000,
        forall|i: int| 0 <= i < values.len() ==> -100_000 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> -100_000 <= #[trigger] values[k] <= 100_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> -100_000 <= #[trigger] nums[k] <= 100_000,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Single element
            let n = 1;
            let mut v = Vec::new();
            v.push(rng.gen_range_i32(-100_000, 100_000));
            let _ = n;
            v
        }
        1 => {
            // All positive
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
            v
        }
        2 => {
            // All negative
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, -1));
            }
            v
        }
        3 => {
            // Contains zero
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
            let idx = rng.gen_range_usize(0, v.len() - 1);
            v[idx] = 0;
            v
        }
        4 => {
            // Tie case: x and -x both present
            let n = rng.gen_range_usize(2, 30);
            let mut v = Vec::new();
            let x = rng.gen_range_i32(1, 100_000);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
            v[0] = x;
            v[1] = -x;
            v
        }
        5 => {
            // Small absolute values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-5, 5));
            }
            v
        }
        6 => {
            // Boundary values
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                let choice = rng.gen_range_usize(0, 3);
                let x = match choice {
                    0 => 100_000,
                    1 => -100_000,
                    2 => 1,
                    _ => -1,
                };
                v.push(x);
            }
            v
        }
        7 => {
            // Max size
            let n = 1000;
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
            v
        }
        8 => {
            // Tie with 1 and -1
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
            v[0] = -1;
            v[1] = 1;
            v
        }
        9 => {
            // Duplicates of same value
            let n = rng.gen_range_usize(1, 50);
            let x = rng.gen_range_i32(-100_000, 100_000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(x);
            }
            v
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
            v
        }
    }
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
        let values = make_case(&mut rng, mode);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}