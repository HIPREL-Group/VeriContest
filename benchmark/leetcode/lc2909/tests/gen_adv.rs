use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        3 <= values.len() <= 100000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000000,
    ensures
        3 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
{
    let n: usize = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == values.len(),
            3 <= n <= 100000,
            0 <= pos <= n,
            nums.len() == pos,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000000,
            forall |k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == values[k],
        decreases n - pos,
    {
        nums.push(values[pos]);
        pos = pos + 1;
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // minimum length, random
            let n = 3usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000_000));
            }
            v
        }
        1 => {
            // small, designed mountain
            let n = rng.gen_range_usize(3, 10);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let x = rng.gen_range_i32(1, 50);
                v.push(if i == n/2 { 100 } else { x });
            }
            v
        }
        2 => {
            // strictly increasing - no mountain
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i as i32) + 1);
            }
            v
        }
        3 => {
            // strictly decreasing - no mountain
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((n as i32) - (i as i32));
            }
            v
        }
        4 => {
            // all same - no mountain
            let n = rng.gen_range_usize(3, 100);
            let val = rng.gen_range_i32(1, 100_000_000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(val); }
            v
        }
        5 => {
            // peak in middle, very small edges
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            let peak_idx = n / 2;
            for i in 0..n {
                if i == peak_idx {
                    v.push(100_000_000);
                } else {
                    v.push(1);
                }
            }
            v
        }
        6 => {
            // random with values 1..100
            let n = rng.gen_range_usize(3, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            v
        }
        7 => {
            // large test
            let n = 100_000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100_000_000)); }
            v
        }
        8 => {
            // large test with easy mountain at specific position
            let n = 100_000usize;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i == 1 {
                    v.push(100_000_000);
                } else {
                    v.push(rng.gen_range_i32(1, 50_000_000));
                }
            }
            v
        }
        9 => {
            // two peaks
            let n = rng.gen_range_usize(6, 200);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i == n/4 || i == 3*n/4 {
                    v.push(100_000_000);
                } else {
                    v.push(rng.gen_range_i32(1, 1000));
                }
            }
            v
        }
        _ => {
            // adversarial: minimum sum candidates
            let n = rng.gen_range_usize(5, 500);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                // create multiple mountain candidates
                if i % 3 == 1 {
                    v.push(rng.gen_range_i32(50, 100));
                } else {
                    v.push(rng.gen_range_i32(1, 40));
                }
            }
            let _ = t;
            v
        }
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
        let values = build_mode(&mut rng, mode, t);
        // Sanity: must be between 3 and 100000, values between 1 and 1e8.
        if values.len() < 3 || values.len() > 100_000 { continue; }
        let mut ok = true;
        for &x in &values {
            if x < 1 || x > 100_000_000 { ok = false; break; }
        }
        if !ok { continue; }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}