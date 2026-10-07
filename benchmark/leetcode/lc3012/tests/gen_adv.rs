use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all ones
            for _ in 0..n {
                v.push(1);
            }
        }
        1 => {
            // all same large
            let x = rng.gen_range_i32(1, 1_000_000_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        2 => {
            // minimum appears exactly once, rest multiples
            let m = rng.gen_range_i32(1, 100);
            v.push(m);
            for _ in 1..n {
                let k = rng.gen_range_i32(1, 1_000_000_000 / m.max(1));
                v.push(m * k);
            }
        }
        3 => {
            // minimum appears multiple times, rest multiples (divisible case)
            let m = rng.gen_range_i32(1, 1000);
            let count_m = rng.gen_range_usize(2, n.min(10).max(2));
            for _ in 0..count_m {
                v.push(m);
            }
            for _ in count_m..n {
                let k = rng.gen_range_i32(1, 1_000_000_000 / m.max(1));
                v.push(m * k);
            }
        }
        4 => {
            // minimum with some non-divisible (should return 1)
            let m = rng.gen_range_i32(2, 1000);
            v.push(m);
            for _ in 1..n {
                let x = rng.gen_range_i32(m + 1, 1_000_000_000);
                v.push(x);
            }
        }
        5 => {
            // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
        }
        6 => {
            // small values
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
        }
        7 => {
            // two values, one divides the other
            let a = rng.gen_range_i32(1, 1000);
            let b = a * rng.gen_range_i32(2, 1000);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(a);
                } else {
                    v.push(b);
                }
            }
        }
        8 => {
            // large values, all maxed
            for _ in 0..n {
                v.push(1_000_000_000);
            }
        }
        9 => {
            // example-like: [1,4,3,1]
            let base = [1, 4, 3, 1, 5, 5, 5, 10, 5, 2, 3, 4];
            for i in 0..n {
                v.push(base[i % base.len()]);
            }
        }
        _ => {
            // single element
            v.push(rng.gen_range_i32(1, 1_000_000_000));
            for _ in 1..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
        }
    }
    // ensure size n
    while v.len() < n {
        v.push(1);
    }
    v.truncate(n);
    // sanity clamp
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 1_000_000_000 { *x = 1_000_000_000; }
    }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 5),
            1 => 100_000,
            2 => 2 + (t % 20),
            3 => 50,
            4 => 10,
            5 => 100,
            6 => 1000,
            7 => 500,
            8 => 100_000,
            9 => 12,
            _ => 1 + (t % 100),
        };
        let n = n.max(1).min(100_000);

        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}