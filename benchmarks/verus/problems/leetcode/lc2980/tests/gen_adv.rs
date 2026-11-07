use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    evens: u8,  // 0, 1, or 2+ number of evens we want
    seed_vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= n <= 100,
        seed_vals.len() == n,
        forall |i: int| 0 <= i < seed_vals.len() ==> 1 <= #[trigger] seed_vals[i] <= 100,
    ensures
        2 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            2 <= n <= 100,
            seed_vals.len() == n,
            nums.len() == i,
            forall |k: int| 0 <= k < seed_vals.len() ==> 1 <= #[trigger] seed_vals[k] <= 100,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        let v = seed_vals[i];
        nums.push(v);
        i = i + 1;
    }
    let _ = evens;
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
}

fn build_vals(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all odd
            for _ in 0..n {
                let x = rng.gen_range_usize(1, 50) * 2 - 1; // 1..=99 odd
                v.push(x as i32);
            }
        }
        1 => {
            // all even
            for _ in 0..n {
                let x = rng.gen_range_usize(1, 50) * 2; // 2..=100 even
                v.push(x as i32);
            }
        }
        2 => {
            // exactly one even
            let pos = rng.gen_range_usize(0, n - 1);
            for i in 0..n {
                if i == pos {
                    let x = rng.gen_range_usize(1, 50) * 2;
                    v.push(x as i32);
                } else {
                    let x = rng.gen_range_usize(1, 50) * 2 - 1;
                    v.push(x as i32);
                }
            }
        }
        3 => {
            // exactly two evens
            let i1 = rng.gen_range_usize(0, n - 1);
            let mut i2 = rng.gen_range_usize(0, n - 2);
            if i2 >= i1 { i2 += 1; }
            for i in 0..n {
                if i == i1 || i == i2 {
                    let x = rng.gen_range_usize(1, 50) * 2;
                    v.push(x as i32);
                } else {
                    let x = rng.gen_range_usize(1, 50) * 2 - 1;
                    v.push(x as i32);
                }
            }
        }
        4 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        5 => {
            // all hundreds
            for _ in 0..n { v.push(100); }
        }
        6 => {
            // alternating
            for i in 0..n {
                if i % 2 == 0 { v.push(2); } else { v.push(3); }
            }
        }
        7 => {
            // powers of 2
            let pows: [i32; 7] = [1, 2, 4, 8, 16, 32, 64];
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, 6);
                v.push(pows[idx]);
            }
        }
        8 => {
            // only odd primes + 1s
            let odds: [i32; 10] = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, 9);
                v.push(odds[idx]);
            }
        }
        9 => {
            // only one even, rest odd - edge case
            for i in 0..n {
                if i == 0 { v.push(2); } else { v.push(1); }
            }
        }
        _ => {
            // fully random
            for _ in 0..n {
                let x = rng.gen_range_usize(1, 100);
                v.push(x as i32);
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 7 {
            0 => 2,
            1 => 3,
            2 => 100,
            3 => 99,
            4 => 10,
            5 => 50,
            _ => 2 + rng.gen_range_usize(0, 98),
        };
        let vals = build_vals(&mut rng, n, mode);
        let nums = generate_test_case(n, 0, &vals);
        print_json(&nums);
    }
}