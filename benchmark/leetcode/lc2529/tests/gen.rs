use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 2000,
        forall|i: int| 0 <= i < result.len() ==> -2000 <= #[trigger] result[i] <= 2000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 2000 { 2000usize } else { values.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 2000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> -2000 <= #[trigger] result[j] <= 2000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] <= result[k],
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let mut value = if value < -2000 { -2000 } else if value > 2000 { 2000 } else { value };
        if i > 0 && value < result[i - 1] { value = result[i - 1]; }
        assert forall|j: int| 0 <= j < result.len() implies result[j] <= value by {
            if j < i - 1 { assert(result[j] <= result[(i - 1) as int]); }
        }
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 2000,
        forall|i: int| 0 <= i < nums.len() ==> -2000 <= #[trigger] nums[i] <= 2000,
    ensures
        1 <= result.len() <= 2000,
        forall|i: int| 0 <= i < result.len() ==> -2000 <= #[trigger] result[i] <= 2000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // nudge last element up (if < 2000)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 2000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 2 {
        // nudge last element down (if > -2000)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > -2000 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 2000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to -1 (all negative)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 2000,
                forall|j: int| 0 <= j < i ==> d[j] == -1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, -1);
            i += 1;
        }
        d
    } else if mutation_kind == 5 {
        // set all elements to 1 (all positive)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 2000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 6 && nums.len() < 2000 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 7 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // set first element to -2000 (min boundary)
        let mut d = nums;
        d.set(0, -2000);
        d
    } else if mutation_kind == 9 {
        // set first element to 2000 (max boundary)
        let mut d = nums;
        d.set(0, 2000);
        d
    } else if mutation_kind == 10 {
        // negate last element (if result in range)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] >= -2000 && d[last] <= 2000 {
            // -d[last] is in range since -2000 <= d[last] <= 2000
            d.set(last, -d[last]);
        }
        d
    } else {
        // fallback: identity
        nums
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_candidate(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-2000, 2000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2529);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let nums = generate_test_case(nums);
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::maximum_count(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![-2, -1, -1, 1, 2, 3],
        vec![-3, -2, -1, 0, 0, 1, 2],
        vec![5, 20, 66, 1314],
    ];

    // Boundary / interesting seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![-1],
        vec![-2000],
        vec![2000],
        vec![0, 0, 0],
        vec![-2000, -1, 0, 1, 2000],
        vec![-1, -1, -1, -1],
        vec![1, 1, 1, 1],
        vec![-2000, 2000],
        vec![-1, 0, 1],
        vec![-1000, -500, 0, 500, 1000],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Emit examples with identity mutation
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 500),      // large
            _ => rng.gen_range_usize(501, 2000),     // max
        };
        let seed_nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(seed_nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
