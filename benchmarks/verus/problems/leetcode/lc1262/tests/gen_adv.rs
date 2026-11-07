use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 40000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10000,
    ensures
        1 <= nums.len() <= 40000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 10000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 10000,
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

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10000));
            }
        }
        1 => {
            for _ in 0..n { v.push(1); }
        }
        2 => {
            for _ in 0..n { v.push(10000); }
        }
        3 => {
            for _ in 0..n { v.push(3); }
        }
        4 => {
            // all multiples of 3
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 3333);
                v.push(x * 3);
            }
        }
        5 => {
            // all == 1 mod 3
            for _ in 0..n {
                let base = rng.gen_range_i32(0, 3332);
                let x = base * 3 + 1;
                if x >= 1 && x <= 10000 { v.push(x); } else { v.push(1); }
            }
        }
        6 => {
            // all == 2 mod 3
            for _ in 0..n {
                let base = rng.gen_range_i32(0, 3332);
                let x = base * 3 + 2;
                if x >= 1 && x <= 10000 { v.push(x); } else { v.push(2); }
            }
        }
        7 => {
            // small values
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 5));
            }
        }
        8 => {
            // mix of large values
            for _ in 0..n {
                v.push(rng.gen_range_i32(9000, 10000));
            }
        }
        9 => {
            // alternating mod residues
            for i in 0..n {
                let r = (i % 3) as i32;
                let base = rng.gen_range_i32(1, 3000);
                let x = base * 3 + r;
                if x >= 1 && x <= 10000 { v.push(x); } else { v.push(r + 1); }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
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
            0 => rng.gen_range_usize(1, 50),
            1 => if t % 2 == 0 { 1 } else { 40000 },
            2 => 100,
            3 => rng.gen_range_usize(1, 30),
            4 => rng.gen_range_usize(1, 100),
            5 => rng.gen_range_usize(1, 100),
            6 => rng.gen_range_usize(1, 100),
            7 => rng.gen_range_usize(1, 500),
            8 => 1000,
            9 => rng.gen_range_usize(1, 200),
            _ => rng.gen_range_usize(1, 40000),
        };
        let n = if n < 1 { 1 } else if n > 40000 { 40000 } else { n };

        let values = build_values(&mut rng, mode, n);
        // Safety clamp
        let mut clamped: Vec<i32> = Vec::with_capacity(values.len());
        for &x in &values {
            let y = if x < 1 { 1 } else if x > 10000 { 10000 } else { x };
            clamped.push(y);
        }
        let nums = generate_test_case(&clamped);
        print_json(&nums);
    }
}