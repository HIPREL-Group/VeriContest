use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    seed_vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        3 <= len <= 100,
        seed_vals.len() == len,
        forall|i: int| 0 <= i < seed_vals.len() ==> 1 <= #[trigger] seed_vals[i] <= 1000,
    ensures
        3 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            3 <= len <= 100,
            seed_vals.len() == len,
            nums.len() == i,
            forall|k: int| 0 <= k < seed_vals.len() ==> 1 <= #[trigger] seed_vals[k] <= 1000,
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
        decreases len - i,
    {
        nums.push(seed_vals[i]);
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

fn build(rng: &mut Rng, mode: usize, t: usize) -> (usize, Vec<i32>) {
    let n: usize = match mode {
        0 => 3,
        1 => 100,
        2 => rng.gen_range_usize(3, 10),
        3 => rng.gen_range_usize(3, 100),
        _ => rng.gen_range_usize(3, 100),
    };

    let mut vals: Vec<i32> = Vec::with_capacity(n);

    match mode {
        0 => {
            // all equal
            let v = rng.gen_range_i32(1, 1000);
            for _ in 0..n { vals.push(v); }
        }
        1 => {
            // all distinct
            for i in 0..n { vals.push((i as i32) + 1); }
        }
        2 => {
            // two distinct values
            let a = rng.gen_range_i32(1, 1000);
            let mut b = rng.gen_range_i32(1, 1000);
            if b == a { b = if a == 1000 { 1 } else { a + 1 }; }
            for i in 0..n {
                vals.push(if i % 2 == 0 { a } else { b });
            }
        }
        3 => {
            // three distinct values pattern
            let a = 1i32;
            let b = 2i32;
            let c = 3i32;
            for i in 0..n {
                let v = match i % 3 { 0 => a, 1 => b, _ => c };
                vals.push(v);
            }
        }
        4 => {
            // boundary values 1 and 1000
            for i in 0..n {
                vals.push(if i % 2 == 0 { 1 } else { 1000 });
            }
        }
        5 => {
            // mostly same with one different
            let v = rng.gen_range_i32(1, 1000);
            for _ in 0..n { vals.push(v); }
            let idx = rng.gen_range_usize(0, n - 1);
            vals[idx] = if v == 1000 { 1 } else { v + 1 };
        }
        6 => {
            // example 1
            // [4,4,2,4,3]
            let pat = [4i32,4,2,4,3];
            for i in 0..n {
                vals.push(pat[i % 5]);
            }
        }
        7 => {
            // small range 1..=3
            for _ in 0..n {
                vals.push(rng.gen_range_i32(1, 3));
            }
        }
        8 => {
            // sorted ascending with duplicates
            let mut cur = 1i32;
            for i in 0..n {
                if i > 0 && rng.next_u64() % 3 == 0 && cur < 1000 {
                    cur += 1;
                }
                vals.push(cur);
            }
        }
        9 => {
            // random full range
            for _ in 0..n {
                vals.push(rng.gen_range_i32(1, 1000));
            }
        }
        _ => {
            // seed-biased
            let _ = t;
            for _ in 0..n {
                vals.push(rng.gen_range_i32(1, 10));
            }
        }
    }

    // clamp all values to [1, 1000] just in case
    for i in 0..vals.len() {
        if vals[i] < 1 { vals[i] = 1; }
        if vals[i] > 1000 { vals[i] = 1000; }
    }

    (n, vals)
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
        let (n, vals) = build(&mut rng, mode, t);
        let nums = generate_test_case(n, &vals);
        print_json(&nums);
    }
}