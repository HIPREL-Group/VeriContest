use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> -1_000_000_000 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -1_000_000_000 <= #[trigger] values[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn clamp_i32(v: i64) -> i32 {
    let lo = -1_000_000_000i64;
    let hi = 1_000_000_000i64;
    if v < lo { lo as i32 } else if v > hi { hi as i32 } else { v as i32 }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // no zeros
            for _ in 0..n {
                let mut x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                if x == 0 { x = 1; }
                v.push(clamp_i32(x));
            }
        }
        2 => {
            // single element, zero
            v.push(0);
            for _ in 1..n {
                let x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                v.push(clamp_i32(x));
            }
        }
        3 => {
            // alternating 0 and non-zero
            for i in 0..n {
                if i % 2 == 0 { v.push(0); } else {
                    let mut x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                    if x == 0 { x = 1; }
                    v.push(clamp_i32(x));
                }
            }
        }
        4 => {
            // runs of zeros separated by non-zero
            let mut i = 0;
            while i < n {
                let run = rng.gen_range_usize(1, 10).min(n - i);
                for _ in 0..run { v.push(0); i += 1; }
                if i < n {
                    let mut x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                    if x == 0 { x = 1; }
                    v.push(clamp_i32(x));
                    i += 1;
                }
            }
        }
        5 => {
            // leading zeros then non-zero
            let k = n / 2;
            for _ in 0..k { v.push(0); }
            for _ in k..n {
                let mut x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                if x == 0 { x = 1; }
                v.push(clamp_i32(x));
            }
        }
        6 => {
            // trailing zeros
            let k = n / 2;
            for _ in 0..k {
                let mut x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                if x == 0 { x = 1; }
                v.push(clamp_i32(x));
            }
            for _ in k..n { v.push(0); }
        }
        7 => {
            // extreme values mixed with zeros
            for _ in 0..n {
                let choice = rng.next_u64() % 3;
                match choice {
                    0 => v.push(0),
                    1 => v.push(1_000_000_000),
                    _ => v.push(-1_000_000_000),
                }
            }
        }
        8 => {
            // mostly zeros, sparse non-zero
            for i in 0..n {
                if i % 37 == 5 {
                    let mut x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                    if x == 0 { x = 1; }
                    v.push(clamp_i32(x));
                } else {
                    v.push(0);
                }
            }
        }
        9 => {
            // random small values
            for _ in 0..n {
                let x = rng.gen_range_i64(-3, 3);
                v.push(x as i32);
            }
        }
        _ => {
            // fully random
            for _ in 0..n {
                let x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                v.push(clamp_i32(x));
            }
        }
    }
    v.truncate(n);
    while v.len() < n { v.push(0); }
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
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => {
                let pick = t % 4;
                match pick { 0 => 1, 1 => 2, 2 => 100, _ => 1000 }
            }
            1 => 50 + (t % 50),
            2 => 1 + (t % 10),
            3 => 100 + (t % 100),
            4 => 200 + (t % 300),
            5 => 500,
            6 => 1000,
            7 => 100_000,
            8 => 300 + (t % 200),
            9 => 64 + (t % 64),
            _ => 100_000,
        };
        let n = if n < 1 { 1 } else if n > 100_000 { 100_000 } else { n };
        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}