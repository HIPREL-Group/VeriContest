use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 100000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1000000000,
    ensures
        2 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
        nums.len() == values.len(),
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            2 <= n <= 100000,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1000000000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
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

fn gen_case(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n: usize = match mode {
        0 => 2,
        1 => rng.gen_range_usize(2, 10),
        2 => rng.gen_range_usize(50, 200),
        3 => 100000,
        4 => rng.gen_range_usize(100, 1000),
        5 => rng.gen_range_usize(2, 5),
        6 => rng.gen_range_usize(1000, 5000),
        7 => 99999,
        8 => rng.gen_range_usize(10, 100),
        9 => rng.gen_range_usize(2, 50),
        _ => rng.gen_range_usize(2, 500),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);

    match mode {
        0 => {
            // small random
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
        }
        1 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        2 => {
            // all max
            for _ in 0..n {
                v.push(1_000_000_000);
            }
        }
        3 => {
            // large n, random
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
        4 => {
            // monotonic increasing
            for i in 0..n {
                let val = (i as i64 * 1000).min(1_000_000_000) as i32;
                v.push(val);
            }
        }
        5 => {
            // monotonic decreasing
            for i in 0..n {
                let val = ((n - i) as i64 * 1000).min(1_000_000_000) as i32;
                v.push(val);
            }
        }
        6 => {
            // first element is max, others small
            v.push(1_000_000_000);
            for _ in 1..n {
                v.push(rng.gen_range_i32(0, 10));
            }
        }
        7 => {
            // last element is max, others small
            for _ in 0..(n - 1) {
                v.push(rng.gen_range_i32(0, 10));
            }
            v.push(1_000_000_000);
        }
        8 => {
            // alternating 0 and large
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(rng.gen_range_i32(1, 1_000_000_000));
                }
            }
        }
        9 => {
            // one spike in the middle
            for _ in 0..n {
                v.push(1);
            }
            let mid = n / 2;
            v[mid] = 1_000_000_000;
        }
        _ => {
            // medium random with occasional big value
            for _ in 0..n {
                let r = rng.next_u64() % 10;
                if r == 0 {
                    v.push(rng.gen_range_i32(500_000_000, 1_000_000_000));
                } else {
                    v.push(rng.gen_range_i32(0, 1000));
                }
            }
        }
    }

    // clamp safety
    for i in 0..v.len() {
        if v[i] < 0 { v[i] = 0; }
        if v[i] > 1_000_000_000 { v[i] = 1_000_000_000; }
    }

    let _ = t;
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
        let values = gen_case(&mut rng, mode, t);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}