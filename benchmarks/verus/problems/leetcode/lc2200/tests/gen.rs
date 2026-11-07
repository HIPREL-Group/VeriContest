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
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= nums.len() <= 1000,
        0 <= k <= 1000,
    ensures
        result.0.len() <= 2147483647usize,
        0 <= result.2,
{
    if mutation_kind == 0 {
        // identity
        (nums, key, k)
    } else if mutation_kind == 1 && k < 1000 {
        // nudge k up
        (nums, key, k + 1)
    } else if mutation_kind == 2 && k > 0 {
        // nudge k down
        (nums, key, k - 1)
    } else if mutation_kind == 3 {
        // k = 0 (only exact index matches)
        (nums, key, 0)
    } else if mutation_kind == 4 && nums.len() < 1000 {
        // grow array: push key value
        let mut n = nums;
        n.push(key);
        (n, key, k)
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink array: pop last element
        let mut n = nums;
        n.pop();
        (n, key, k)
    } else if mutation_kind == 6 {
        // set first element to key
        let mut n = nums;
        n.set(0, key);
        (n, key, k)
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first two elements
        let mut n = nums;
        let tmp = n[0];
        n.set(0, n[1]);
        n.set(1, tmp);
        (n, key, k)
    } else if mutation_kind == 8 {
        // set all elements to key
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                1 <= n.len() <= 1000,
            decreases n.len() - i,
        {
            n.set(i, key);
            i += 1;
        }
        (n, key, k)
    } else if mutation_kind == 9 {
        // k = nums.len() as i32 - 1 (maximum useful k)
        let new_k = (nums.len() - 1) as i32;
        (nums, key, new_k)
    } else {
        // fallback: identity
        (nums, key, k)
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

fn mutate(nums: Vec<i32>, key: i32, k: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_candidate(nums, key, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 1000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2200);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, key: i32, k: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        let (nums, key, k) = generate_test_case(nums, key, k);
        if *count >= target {
            return;
        }
        let input_key = format!("{:?}-{}-{}", nums, key, k);
        if !seen.insert(input_key) {
            return;
        }
        let output = Solution::find_k_distant_indices(nums.clone(), key, k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "key": key, "k": k},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![3,4,9,1,3,9,5], 9, 1, &mut seen, &mut out, &mut count);
    emit(vec![2,2,2,2,2], 2, 2, &mut seen, &mut out, &mut count);

    // Curated seed inputs for diversity
    let seeds: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![1], 1, 0),
        (vec![1], 1, 1),
        (vec![1], 2, 0),
        (vec![1, 2, 3], 2, 0),
        (vec![1, 2, 3], 2, 1),
        (vec![1, 2, 3], 3, 2),
        (vec![5, 5, 5], 5, 0),
        (vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1, 5),
        (vec![1, 2, 1, 2, 1], 1, 1),
        (vec![999, 1, 999, 1, 999], 999, 0),
        (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 5, 3),
        (vec![1000; 100], 1000, 100),
        (vec![1, 1000], 1, 0),
        (vec![1, 1000], 1000, 0),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for (nums, key, k) in &seeds {
        for &mk in &mutation_kinds {
            let (rn, rk, rv) = mutate(nums.clone(), *key, *k, mk);
            emit(rn, rk, rv, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with random mutations across size classes
    while count < target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };
        let nums = random_nums(&mut rng, len);
        // Pick key from the array ~80% of the time, random otherwise
        let key = if rng.gen_range_usize(0, 4) > 0 {
            let idx = rng.gen_range_usize(0, nums.len() - 1);
            nums[idx]
        } else {
            rng.gen_range_i64(1, 1000) as i32
        };
        let k = rng.gen_range_i64(0, len as i64) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (rn, rk, rv) = mutate(nums, key, k, mk);
        emit(rn, rk, rv, &mut seen, &mut out, &mut count);
    }
}
