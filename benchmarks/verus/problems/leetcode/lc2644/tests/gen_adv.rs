use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    divisors: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums.len() <= 1000,
        1 <= divisors.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < divisors.len() ==> 1 <= #[trigger] divisors[i] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1_000_000_000,
{
    (nums, divisors)
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

fn build_test(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    let mut nums: Vec<i32> = Vec::new();
    let mut divisors: Vec<i32> = Vec::new();

    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let m = rng.gen_range_usize(1, 10);
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100));
            }
            for _ in 0..m {
                divisors.push(rng.gen_range_i32(1, 20));
            }
        }
        1 => {
            // single elements
            nums.push(rng.gen_range_i32(1, 1_000_000_000));
            divisors.push(rng.gen_range_i32(1, 1_000_000_000));
        }
        2 => {
            // max sizes
            for _ in 0..1000 {
                nums.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            for _ in 0..1000 {
                divisors.push(rng.gen_range_i32(1, 1_000_000_000));
            }
        }
        3 => {
            // all 1's in nums
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                nums.push(1);
            }
            for _ in 0..m {
                divisors.push(rng.gen_range_i32(1, 100));
            }
        }
        4 => {
            // all 1's in divisors
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            for _ in 0..m {
                divisors.push(1);
            }
        }
        5 => {
            // duplicates - tiebreak test (smallest)
            let m = rng.gen_range_usize(2, 50);
            let n = rng.gen_range_usize(1, 50);
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100) * 6);
            }
            // multiple equal divisors
            for _ in 0..m {
                let v = rng.gen_range_i32(1, 5);
                divisors.push(v);
            }
        }
        6 => {
            // large divisors that don't divide
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100));
            }
            for _ in 0..m {
                divisors.push(rng.gen_range_i32(500_000_000, 1_000_000_000));
            }
        }
        7 => {
            // common divisor scenario
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(2, 50);
            let factor = rng.gen_range_i32(2, 10);
            for _ in 0..n {
                nums.push(factor * rng.gen_range_i32(1, 100));
            }
            for _ in 0..m {
                divisors.push(rng.gen_range_i32(1, 20));
            }
        }
        8 => {
            // descending divisors with same score
            let n = rng.gen_range_usize(1, 50);
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 1_000));
            }
            // divisors in descending order
            for k in 0..20 {
                divisors.push(20 - k);
            }
        }
        9 => {
            // ascending divisors
            let n = rng.gen_range_usize(1, 50);
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 1_000));
            }
            for k in 0..20 {
                divisors.push(k + 1);
            }
        }
        _ => {
            // generic random
            let n = rng.gen_range_usize(1, 1000);
            let m = rng.gen_range_usize(1, 1000);
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            for _ in 0..m {
                divisors.push(rng.gen_range_i32(1, 1_000_000_000));
            }
        }
    }

    // Ensure non-empty
    if nums.is_empty() {
        nums.push(1);
    }
    if divisors.is_empty() {
        divisors.push(1);
    }
    // Truncate if needed
    if nums.len() > 1000 {
        nums.truncate(1000);
    }
    if divisors.len() > 1000 {
        divisors.truncate(1000);
    }
    // Ensure value bounds
    for i in 0..nums.len() {
        if nums[i] < 1 {
            nums[i] = 1;
        } else if nums[i] > 1_000_000_000 {
            nums[i] = 1_000_000_000;
        }
    }
    for i in 0..divisors.len() {
        if divisors[i] < 1 {
            divisors[i] = 1;
        } else if divisors[i] > 1_000_000_000 {
            divisors[i] = 1_000_000_000;
        }
    }

    (nums, divisors)
}

fn print_json(nums: &[i32], divisors: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"divisors\":[");
    for i in 0..divisors.len() {
        if i > 0 { print!(","); }
        print!("{}", divisors[i]);
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
        let (nums, divisors) = build_test(&mut rng, mode);
        let (n2, d2) = generate_test_case(nums, divisors);
        print_json(&n2, &d2);
    }
}