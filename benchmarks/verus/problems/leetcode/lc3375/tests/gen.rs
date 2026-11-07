use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        1 <= k <= 100,
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set all elements to k (all_ge_k satisfied, count_distinct = 0 → answer 0)
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100,
                1 <= k <= 100,
                forall|j: int| 0 <= j < i ==> v[j] == k,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
                forall|j: int| i <= j < v.len() ==> 1 <= #[trigger] v[j] <= 100,
            decreases v.len() - i,
        {
            v.set(i, k);
            i += 1;
        }
        (v, k)
    } else if mutation_kind == 2 && nums.len() > 1 {
        // shrink: remove last element
        let mut v = nums;
        v.pop();
        (v, k)
    } else if mutation_kind == 3 && nums.len() < 100 {
        // grow: push k (always valid element)
        let mut v = nums;
        v.push(k);
        (v, k)
    } else if mutation_kind == 4 {
        // set first element to 1 (below k if k > 1 → triggers -1 result)
        let mut v = nums;
        v.set(0, 1i32);
        (v, k)
    } else if mutation_kind == 5 {
        // set first element to 100 (max boundary)
        let mut v = nums;
        v.set(0, 100i32);
        (v, k)
    } else if mutation_kind == 6 {
        // nudge k up: if k < 100, use k+1
        if k < 100 {
            (nums, k + 1)
        } else {
            (nums, k)
        }
    } else if mutation_kind == 7 {
        // nudge k down: if k > 1, use k-1
        if k > 1 {
            (nums, k - 1)
        } else {
            (nums, k)
        }
    } else if mutation_kind == 8 {
        // set k to 1 (min boundary)
        (nums, 1i32)
    } else if mutation_kind == 9 {
        // set k to 100 (max boundary)
        (nums, 100i32)
    } else if mutation_kind == 10 {
        // set last element to k-1 if k > 1 (ensure at least one element < k → -1)
        if k > 1 {
            let mut v = nums;
            let last = v.len() - 1;
            v.set(last, k - 1);
            (v, k)
        } else {
            (nums, k)
        }
    } else if mutation_kind == 11 {
        // swap first and last elements
        if nums.len() > 1 {
            let mut v = nums;
            let last = v.len() - 1;
            let first_val = v[0];
            let last_val = v[last];
            v.set(0, last_val);
            v.set(last, first_val);
            (v, k)
        } else {
            (nums, k)
        }
    } else {
        // fallback: identity
        (nums, k)
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3375);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?},{}", nums, k);
        if !seen.insert(key) { return; }
        let output = Solution::min_operations(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![5, 2, 5, 4, 5], 2),
        (vec![2, 1, 2], 2),
        (vec![9, 7, 5, 3], 1),
    ];
    for (nums, k) in &examples {
        emit(nums.clone(), *k, &mut seen, &mut out, &mut count);
    }

    // Seed inputs: interesting configurations
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![100], 100),
        (vec![100], 1),
        (vec![1], 100),
        (vec![50, 50, 50], 50),
        (vec![1, 2, 3, 4, 5], 1),
        (vec![1, 2, 3, 4, 5], 5),
        (vec![100, 99, 98, 97], 97),
        (vec![1, 1, 1, 1, 1], 1),
        (vec![1, 1, 1, 1, 1], 2),
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply every mutation to every seed
    for (nums, k) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = generate_test_case(nums.clone(), *k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with random mutations
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),     // tiny
            1 => rng.gen_range_usize(1, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };
        let nums = random_nums(&mut rng, len);
        let k = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (result_nums, result_k) = generate_test_case(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
