use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= raw.len() <= 20_000,
    ensures
        1 <= nums.len() <= 20_000,
        forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = raw.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == raw.len(),
            1 <= n <= 20_000,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
        decreases n - i,
    {
        let v = raw[i];
        let clamped: i32 = if v > 1_000_000_000 {
            1_000_000_000
        } else if v < -1_000_000_000 {
            -1_000_000_000
        } else {
            v
        };
        nums.push(clamped);
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
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // tiny random
            let n = rng.gen_range_usize(1, 5);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10, 10));
            }
            v
        }
        1 => {
            // strictly increasing - no 132 pattern
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(i as i32);
            }
            v
        }
        2 => {
            // strictly decreasing - no 132 pattern
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((n - i) as i32);
            }
            v
        }
        3 => {
            // classic 132 example
            vec![3, 1, 4, 2]
        }
        4 => {
            // all equal - no 132
            let n = rng.gen_range_usize(1, 100);
            let val = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            vec![val; n]
        }
        5 => {
            // single element
            vec![rng.gen_range_i32(-1_000_000_000, 1_000_000_000)]
        }
        6 => {
            // max values
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(1_000_000_000);
                } else {
                    v.push(-1_000_000_000);
                }
            }
            v
        }
        7 => {
            // large random
            let n = rng.gen_range_usize(100, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
            v
        }
        8 => {
            // maximum size
            let n = 20_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
            v
        }
        9 => {
            // almost sorted with one swap to create 132
            let n = rng.gen_range_usize(3, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(i as i32);
            }
            if n >= 3 {
                let i = rng.gen_range_usize(1, n - 2);
                let j = i + 1;
                v.swap(i, j);
            }
            v
        }
        10 => {
            // contains obvious 132 at start
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            v.push(1);
            v.push(4);
            v.push(2);
            for _ in 3..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
            // seed with t for variation
            if v.len() > 0 {
                v[0] = (t as i32) % 1000;
            }
            v
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 12usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let raw = gen_mode(&mut rng, mode, t);
        let nums = generate_test_case(&raw);
        print_json(&nums);
    }
}