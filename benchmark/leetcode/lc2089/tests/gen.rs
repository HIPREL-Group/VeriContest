use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 100 { 100usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 100,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 100 { 100 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(nums: Vec<i32>, target: i32) -> (result: (Vec<i32>, i32))
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
{
    let nums = bounded_values(&nums);
    let target = if target < 1 { 1 } else if target > 100 { 100 } else { target };
    (nums, target)
}


pub fn generate_candidate(
    nums: Vec<i32>,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        nums.len() <= 100,
    ensures
        result.0.len() <= 2147483647usize,
{
    if mutation_kind == 0 {
        // identity
        (nums, target)
    } else if mutation_kind == 1 && nums.len() < 100 {
        // grow: push target into the array
        let mut d = nums;
        d.push(target);
        (d, target)
    } else if mutation_kind == 2 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        (d, target)
    } else if mutation_kind == 3 && nums.len() > 0 {
        // set first element to target
        let mut d = nums;
        d.set(0, target);
        (d, target)
    } else if mutation_kind == 4 && nums.len() > 0 {
        // set last element to target
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, target);
        (d, target)
    } else if mutation_kind == 5 {
        // change target to 0
        (nums, 0)
    } else if mutation_kind == 6 && nums.len() > 0 {
        // nudge target to first element value
        let t = nums[0];
        (nums, t)
    } else if mutation_kind == 7 {
        // negate target
        let neg = if target > i32::MIN { (0i32 - target) } else { target };
        (nums, neg)
    } else if mutation_kind == 8 && nums.len() > 0 {
        // set all elements to target
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                d.len() <= 100,
            decreases d.len() - i,
        {
            d.set(i, target);
            i += 1;
        }
        (d, target)
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        (d, target)
    } else {
        // fallback: identity
        (nums, target)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn mutate(nums: Vec<i32>, target: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_candidate(nums, target, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2089);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, target: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let (nums, target) = generate_test_case(nums, target);
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", nums, target);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::target_indices(nums.clone(), target);
        writeln!(out, "{}", json!({"input": {"nums": nums, "target": target}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 5, 2, 3], 2),
        (vec![1, 2, 5, 2, 3], 3),
        (vec![1, 2, 5, 2, 3], 5),
    ];
    for (nums, target) in &examples {
        emit(nums.clone(), *target, &mut seen, &mut out, &mut count);
    }

    // Curated seeds with diverse structure
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1], 2),
        (vec![100], 100),
        (vec![1, 1, 1, 1], 1),
        (vec![1, 2, 3, 4, 5], 3),
        (vec![5, 4, 3, 2, 1], 1),
        (vec![50], 50),
        (vec![1, 100], 50),
        (vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1),
        (vec![99, 100], 100),
        (vec![42, 42, 42], 42),
        (vec![1, 2], 3),
    ];

    let mutation_kinds: Vec<u8> = (0..=9).collect();

    // Apply every mutation to every seed
    for (nums, target) in &seeds {
        for &mk in &mutation_kinds {
            let (r_nums, r_target) = mutate(nums.clone(), *target, mk);
            emit(r_nums, r_target, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations
    for _ in 0..200 {
        if count >= target_count { break; }
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),    // tiny
            1 => rng.gen_range_usize(1, 10),   // small
            2 => rng.gen_range_usize(11, 50),   // medium
            3 => rng.gen_range_usize(51, 100),  // large
            _ => 100,                           // max
        };
        let nums = random_nums(&mut rng, len);
        let target = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (r_nums, r_target) = mutate(nums, target, mk);
        emit(r_nums, r_target, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutation
    while count < target_count {
        let len = rng.gen_range_usize(1, 100);
        let nums = random_nums(&mut rng, len);
        let target = rng.gen_range_i64(1, 100) as i32;
        emit(mutate(nums, target, 0).0, mutate(random_nums(&mut rng, 1), target, 0).1, &mut seen, &mut out, &mut count);
    }
}
