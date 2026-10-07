use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20_000,
        0 <= k < nums.len() as i32,
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 20_000,
        0 <= result.1 < result.0.len() as i32,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set element at k to 1 (minimum value)
        let mut d = nums;
        d.set(k as usize, 1);
        (d, k)
    } else if mutation_kind == 2 {
        // set element at k to 20_000 (maximum value)
        let mut d = nums;
        d.set(k as usize, 20_000);
        (d, k)
    } else if mutation_kind == 3 && (k as usize) + 1 < nums.len() {
        // nudge k up by 1
        (nums, k + 1)
    } else if mutation_kind == 4 && k > 0 {
        // nudge k down by 1
        (nums, k - 1)
    } else if mutation_kind == 5 {
        // k = 0 (left boundary)
        (nums, 0)
    } else if mutation_kind == 6 {
        // k = last index (right boundary)
        let last = (nums.len() - 1) as i32;
        (nums, last)
    } else if mutation_kind == 7 && nums.len() < 100_000 {
        // grow array by one element (push 1), keep k
        let mut d = nums;
        d.push(1);
        (d, k)
    } else if mutation_kind == 8 && nums.len() > 1 && (k as usize) < nums.len() - 1 {
        // shrink array by one element (pop last), keep k
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 9 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 10 {
        // set all elements to 20_000
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 20_000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 20_000);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 11 && nums.len() >= 2 {
        // swap element at k with element at 0
        let mut d = nums;
        let k_idx = k as usize;
        let tmp = d[0];
        d.set(0, d[k_idx]);
        d.set(k_idx, tmp);
        (d, k)
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

fn mutate(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 20_000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1793);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}:{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::maximum_score(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 4, 3, 7, 4, 5], 3),
        (vec![5, 5, 4, 5, 4, 1, 1, 1], 0),
    ];

    for (nums, k) in &examples {
        emit(nums.clone(), *k, &mut seen, &mut out, &mut count);
    }

    // Seed inputs: diverse structures
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 0),                                      // single element
        (vec![20_000], 0),                                 // single max element
        (vec![1, 1], 0),                                   // two minimum elements
        (vec![20_000, 20_000], 1),                         // two max elements
        (vec![1, 20_000, 1], 1),                           // peak at k
        (vec![20_000, 1, 20_000], 1),                      // valley at k
        (vec![1, 2, 3, 4, 5], 2),                          // ascending, k in middle
        (vec![5, 4, 3, 2, 1], 2),                          // descending, k in middle
        (vec![3, 3, 3, 3, 3], 2),                          // all same
        (vec![1, 1, 1, 20_000, 1, 1, 1], 3),              // spike at k
        (vec![10_000, 10_000, 10_000, 10_000, 10_000], 0), // k at start
        (vec![10_000, 10_000, 10_000, 10_000, 10_000], 4), // k at end
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed
    for (nums, k) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = mutate(nums.clone(), *k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with random mutations across size classes
    while count < target_count {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10_000), // very large
        };
        let nums = random_nums(&mut rng, n);
        let k = rng.gen_range_i64(0, (n - 1) as i64) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (result_nums, result_k) = mutate(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
