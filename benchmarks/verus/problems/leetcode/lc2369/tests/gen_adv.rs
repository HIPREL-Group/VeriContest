use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 100000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000000,
    ensures
        2 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000,
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
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000000,
        decreases n - i,
    {
        nums.push(values[i]);
        i += 1;
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
        lo + (self.next_u64() % span) as i32
    }
}

fn build_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn build_all_equal(n: usize, x: i32) -> Vec<i32> {
    vec![x; n]
}

fn build_consecutive_inc(n: usize, start: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let val = start + i as i32;
        let val = if val < 1 { 1 } else if val > 1_000_000 { 1_000_000 } else { val };
        v.push(val);
    }
    v
}

fn build_pairs(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let x = rng.gen_range_i32(1, 1_000_000);
        v.push(x);
        if i + 1 < n {
            v.push(x);
        }
        i += 2;
    }
    v.truncate(n);
    v
}

fn build_triples_equal(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let x = rng.gen_range_i32(1, 1_000_000);
        v.push(x);
        if i + 1 < n { v.push(x); }
        if i + 2 < n { v.push(x); }
        i += 3;
    }
    v.truncate(n);
    v
}

fn build_triples_inc(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let x = rng.gen_range_i32(1, 999_998);
        v.push(x);
        if i + 1 < n { v.push(x + 1); }
        if i + 2 < n { v.push(x + 2); }
        i += 3;
    }
    v.truncate(n);
    v
}

fn build_mixed_valid(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    while v.len() < n {
        let remaining = n - v.len();
        let choice = rng.next_u64() % 3;
        if choice == 0 && remaining >= 2 {
            let x = rng.gen_range_i32(1, 1_000_000);
            v.push(x);
            v.push(x);
        } else if choice == 1 && remaining >= 3 {
            let x = rng.gen_range_i32(1, 1_000_000);
            v.push(x); v.push(x); v.push(x);
        } else if choice == 2 && remaining >= 3 {
            let x = rng.gen_range_i32(1, 999_998);
            v.push(x); v.push(x+1); v.push(x+2);
        } else if remaining >= 2 {
            let x = rng.gen_range_i32(1, 1_000_000);
            v.push(x); v.push(x);
        } else {
            v.push(1);
        }
    }
    v.truncate(n);
    v
}

fn build_bad_len_odd_equal(n: usize, x: i32) -> Vec<i32> {
    // all equal, length that's not expressible as 2a+3b easily? any n>=2 is OK for all-equal
    vec![x; n]
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

    let total = 200;
    for t in 0..total {
        let mode = t % 12;
        let n: usize = match mode {
            0 => 2,
            1 => 3,
            2 => rng.gen_range_usize(2, 20),
            3 => rng.gen_range_usize(2, 100),
            4 => rng.gen_range_usize(2, 1000),
            5 => 100_000,
            6 => rng.gen_range_usize(2, 500),
            7 => rng.gen_range_usize(2, 50),
            8 => rng.gen_range_usize(2, 200),
            9 => rng.gen_range_usize(2, 300),
            10 => rng.gen_range_usize(2, 30),
            _ => rng.gen_range_usize(2, 100),
        };

        let values: Vec<i32> = match mode {
            0 => {
                let x = rng.gen_range_i32(1, 1_000_000);
                vec![x, x]
            }
            1 => {
                let c = rng.next_u64() % 3;
                if c == 0 {
                    let x = rng.gen_range_i32(1, 1_000_000);
                    vec![x, x, x]
                } else if c == 1 {
                    let x = rng.gen_range_i32(1, 999_998);
                    vec![x, x+1, x+2]
                } else {
                    build_random(&mut rng, 3, 1, 1_000_000)
                }
            }
            2 => build_random(&mut rng, n, 1, 5),
            3 => build_random(&mut rng, n, 1, 1_000_000),
            4 => {
                let x = rng.gen_range_i32(1, 1_000_000);
                build_all_equal(n, x)
            }
            5 => {
                // large: all equal
                let x = rng.gen_range_i32(1, 1_000_000);
                build_all_equal(n, x)
            }
            6 => build_consecutive_inc(n, rng.gen_range_i32(1, 500_000)),
            7 => build_pairs(n, &mut rng),
            8 => build_triples_equal(n, &mut rng),
            9 => build_triples_inc(n, &mut rng),
            10 => build_mixed_valid(n, &mut rng),
            _ => {
                // edge values
                let mut v = Vec::with_capacity(n);
                for _ in 0..n {
                    let c = rng.next_u64() % 4;
                    let val = match c {
                        0 => 1,
                        1 => 1_000_000,
                        2 => rng.gen_range_i32(1, 10),
                        _ => rng.gen_range_i32(999_990, 1_000_000),
                    };
                    v.push(val);
                }
                v
            }
        };

        // sanity: clamp
        let mut clean: Vec<i32> = values.into_iter().map(|x| {
            if x < 1 { 1 } else if x > 1_000_000 { 1_000_000 } else { x }
        }).collect();
        if clean.len() < 2 {
            while clean.len() < 2 { clean.push(1); }
        }
        if clean.len() > 100_000 {
            clean.truncate(100_000);
        }

        let nums = generate_test_case(&clean);
        print_json(&nums);
    }
}