use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 5000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 5000,
    ensures
        1 <= nums.len() <= 5000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 5000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 5000,
            forall |k: int| 0 <= k < nums.len() ==> nums[k] == values[k],
            forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 5000,
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

fn build_vec(v: Vec<i32>) -> Vec<i32> { v }

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Smallest case: n = 1
            let v = rng.gen_range_i32(0, 5000);
            vec![v]
        }
        1 => {
            // All even
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let x = rng.gen_range_i32(0, 2500) * 2;
                v.push(x);
            }
            v
        }
        2 => {
            // All odd
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let x = rng.gen_range_i32(0, 2499) * 2 + 1;
                v.push(x);
            }
            v
        }
        3 => {
            // Already partitioned: evens then odds
            let n = rng.gen_range_usize(2, 50);
            let split = rng.gen_range_usize(0, n);
            let mut v = Vec::with_capacity(n);
            for _ in 0..split {
                v.push(rng.gen_range_i32(0, 2500) * 2);
            }
            for _ in split..n {
                let x = rng.gen_range_i32(0, 2499) * 2 + 1;
                v.push(x);
            }
            v
        }
        4 => {
            // Reverse partitioned: odds then evens
            let n = rng.gen_range_usize(2, 50);
            let split = rng.gen_range_usize(0, n);
            let mut v = Vec::with_capacity(n);
            for _ in 0..split {
                let x = rng.gen_range_i32(0, 2499) * 2 + 1;
                v.push(x);
            }
            for _ in split..n {
                v.push(rng.gen_range_i32(0, 2500) * 2);
            }
            v
        }
        5 => {
            // Alternating
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(0, 2500) * 2);
                } else {
                    let x = rng.gen_range_i32(0, 2499) * 2 + 1;
                    v.push(x);
                }
            }
            v
        }
        6 => {
            // Max size
            let n = 5000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 5000));
            }
            v
        }
        7 => {
            // All zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        8 => {
            // Boundary values only
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let pick = rng.gen_range_usize(0, 3);
                let x = match pick {
                    0 => 0,
                    1 => 1,
                    2 => 4999,
                    _ => 5000,
                };
                v.push(x);
            }
            v
        }
        9 => {
            // Single even / single odd edge cases
            let pick = rng.gen_range_usize(0, 1);
            if pick == 0 {
                vec![rng.gen_range_i32(0, 2500) * 2]
            } else {
                let x = rng.gen_range_i32(0, 2499) * 2 + 1;
                vec![x]
            }
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 5000));
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
        let values = build_vec(gen_mode(&mut rng, mode));
        // Safety: ensure constraints
        if values.is_empty() || values.len() > 5000 {
            continue;
        }
        let mut ok = true;
        for &x in &values {
            if x < 0 || x > 5000 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}