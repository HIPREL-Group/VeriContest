use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= len <= 20,
        vals.len() == len,
        forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10_000_000,
    ensures
        1 <= nums.len() <= 20,
        forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 10_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            len == vals.len(),
            1 <= len <= 20,
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10_000_000,
            forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 10_000_000,
            forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == vals[k],
        decreases len - i,
    {
        nums.push(vals[i]);
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
                v.push(rng.gen_range_i32(0, 10_000_000));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(0);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(10_000_000);
            }
        }
        3 => {
            // alternating high/low
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(10_000_000);
                } else {
                    v.push(0);
                }
            }
        }
        4 => {
            // single big peak in middle
            for i in 0..n {
                if i == n / 2 {
                    v.push(10_000_000);
                } else {
                    v.push(rng.gen_range_i32(0, 100));
                }
            }
        }
        5 => {
            // ascending
            for i in 0..n {
                let val = ((i as i64 * 10_000_000) / (n as i64).max(1)) as i32;
                v.push(val.max(0).min(10_000_000));
            }
        }
        6 => {
            // descending
            for i in 0..n {
                let val = (((n - 1 - i) as i64 * 10_000_000) / (n as i64).max(1)) as i32;
                v.push(val.max(0).min(10_000_000));
            }
        }
        7 => {
            // small values
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
        }
        8 => {
            // known examples
            if n == 3 {
                v.push(1); v.push(5); v.push(2);
            } else if n == 4 {
                v.push(1); v.push(5); v.push(233); v.push(7);
            } else {
                for _ in 0..n {
                    v.push(rng.gen_range_i32(0, 10_000_000));
                }
            }
        }
        9 => {
            // two equal ends
            for i in 0..n {
                if i == 0 || i == n - 1 {
                    v.push(10_000_000);
                } else {
                    v.push(rng.gen_range_i32(0, 100));
                }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
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
        let n = match mode {
            0 => rng.gen_range_usize(1, 20),
            1 => 1 + (t % 20),
            2 => 20,
            3 => 1,
            4 => if t % 2 == 0 { 2 } else { 20 },
            5 => 5 + (t % 16),
            6 => 10,
            7 => rng.gen_range_usize(1, 20),
            8 => if t % 2 == 0 { 3 } else { 4 },
            9 => 2 + (t % 19),
            _ => rng.gen_range_usize(1, 20),
        };
        let n = n.max(1).min(20);

        let vals = build_vals(&mut rng, mode, n);
        let nums = generate_test_case(n, &vals);
        print_json(&nums);
    }
}