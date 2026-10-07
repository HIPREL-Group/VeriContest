use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 1000 { 1000usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 1000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 1000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 1000 { 1000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(nums: Vec<i32>, key: i32, k: i32) -> (result: (Vec<i32>, i32, i32))
    ensures
        1 <= result.0.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1 <= 1000,
        exists|i: int| 0 <= i < result.0.len() && result.0[i] == result.1,
        1 <= result.2 <= result.0.len(),
{
    let nums = bounded_values(&nums);
    let k = if k < 1 { 1 } else if k as usize > nums.len() { nums.len() as i32 } else { k };
    let mut index = 0usize;
    let mut i = 0usize;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            1 <= nums.len() <= 1000,
            index < nums.len(),
        decreases nums.len() - i,
    {
        if nums[i] == key { index = i; }
        i += 1;
    }
    let key = nums[index];
    let result = (nums, key, k);
    assert(result.0[index as int] == result.1);
    assert(exists|j: int| 0 <= j < result.0.len() && result.0[j] == result.1);
    result
}


pub fn generate_candidate(
    nums: Vec<i32>,
    key: i32,
    k: i32,
) -> (result: (Vec<i32>, i32, i32))
    requires
        nums.len() >= 1,
        nums.len() <= 1000,
        0 <= k,
        k <= 2_000_000_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    ensures
        result.0.len() == nums.len(),
        result.0.len() <= 2147483647usize,
        0 <= result.2,
        result.1 == key,
        result.2 == k,
{
    (nums, key, k)
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
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32, i32) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 1000,
        3 => rng.gen_range_usize(1, 10),
        4 => rng.gen_range_usize(50, 200),
        5 => 1000,
        6 => rng.gen_range_usize(1, 1000),
        7 => 500,
        8 => rng.gen_range_usize(1, 20),
        9 => 100,
        _ => rng.gen_range_usize(1, 100),
    };

    let key: i32 = match mode {
        0 | 1 => rng.gen_range_i32(1, 1000),
        2 => 1,
        3 => 1000,
        4 => rng.gen_range_i32(1, 10),
        5 => 500,
        6 => rng.gen_range_i32(1, 1000),
        7 => 7,
        8 => rng.gen_range_i32(1, 3),
        9 => 1000,
        _ => rng.gen_range_i32(1, 1000),
    };

    let k: i32 = match mode {
        0 => 1,
        1 => rng.gen_range_i32(1, n as i32),
        2 => n as i32,
        3 => 1,
        4 => rng.gen_range_i32(1, n as i32),
        5 => 1,
        6 => n as i32,
        7 => rng.gen_range_i32(1, n as i32),
        8 => rng.gen_range_i32(1, n as i32),
        9 => n as i32 / 2 + 1,
        _ => rng.gen_range_i32(1, n as i32),
    };

    let mut nums: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let v: i32 = match mode {
            0 | 1 => key,
            2 => if i % 2 == 0 { key } else { rng.gen_range_i32(2, 1000) },
            3 => {
                if i == 0 || i == n - 1 { key } else { rng.gen_range_i32(1, 999) }
            }
            4 => rng.gen_range_i32(1, 10),
            5 => {
                if i == n / 2 { key } else { rng.gen_range_i32(1, 1000) }
            }
            6 => {
                let candidates = [key, rng.gen_range_i32(1, 1000)];
                candidates[(rng.next_u64() as usize) % 2]
            }
            7 => {
                if i % 13 == 0 { 7 } else { rng.gen_range_i32(1, 1000) }
            }
            8 => rng.gen_range_i32(1, 3),
            9 => {
                if i == 0 { key } else { rng.gen_range_i32(1, 999) }
            }
            _ => rng.gen_range_i32(1, 1000),
        };
        let v = if v < 1 { 1 } else if v > 1000 { 1000 } else { v };
        nums.push(v);
    }

    // Ensure key appears in nums (problem constraint says key appears in nums).
    // Find whether key is in nums; if not, replace a random index with key.
    let mut has_key = false;
    for &x in &nums {
        if x == key { has_key = true; break; }
    }
    if !has_key {
        let idx = (rng.next_u64() as usize) % nums.len();
        nums[idx] = key;
    }

    let _ = t;
    (nums, key, k)
}

fn print_json(nums: &[i32], key: i32, k: i32) {
    let (nums, key, k) = generate_test_case(nums.to_vec(), key, k);
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"key\":{},\"k\":{}}}", key, k);
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
        let (nums, key, k) = build_case(&mut rng, mode, t);
        // Call generate_candidate to satisfy verification contract.
        let (vnums, vkey, vk) = generate_candidate(nums, key, k);
        print_json(&vnums, vkey, vk);
    }
}
