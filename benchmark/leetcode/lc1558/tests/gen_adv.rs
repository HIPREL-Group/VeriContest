use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 100000 { 100000usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 1000000000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let value = if value < 0 { 0 } else if value > 1000000000 { 1000000000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums@.len() <= 100_000,
        forall|i: int| 0 <= i < nums@.len() ==> 0 <= #[trigger] nums@[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            1 <= n <= 100_000,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> nums@[k] == values@[k],
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums@[k] <= 1_000_000_000,
        decreases n - i,
    {
        let v = values[i];
        nums.push(v);
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

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
            v
        }
        1 => {
            // Single element
            vec![rng.gen_range_i32(0, 1_000_000_000)]
        }
        2 => {
            // All zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        3 => {
            // Powers of two (only needs doublings, minimal popcount)
            let n = rng.gen_range_usize(1, 30);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let k = rng.gen_range_usize(0, 29);
                v.push(1i32 << k);
            }
            v
        }
        4 => {
            // Max values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(1_000_000_000i32);
            }
            v
        }
        5 => {
            // Maximum length
            let n = 100_000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000_000));
            }
            v
        }
        6 => {
            // Mix of zeros and big numbers
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(rng.gen_range_i32(1, 1_000_000_000));
                }
            }
            v
        }
        7 => {
            // All ones (popcount heavy)
            let n = rng.gen_range_usize(1, 1000);
            vec![1i32; n]
        }
        8 => {
            // Numbers like 2^k - 1 (all bits set)
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let k = rng.gen_range_usize(1, 30);
                v.push((1i32 << k) - 1);
            }
            v
        }
        9 => {
            // Single big element
            vec![rng.gen_range_i32(500_000_000, 1_000_000_000)]
        }
        _ => {
            // Random general
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000_000));
            }
            let _ = t;
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    let nums = generate_test_case(nums.to_vec());
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let values = gen_mode(&mut rng, mode, t);
        let nums = generate_candidate(&values);
        print_json(&nums);
    }
}
