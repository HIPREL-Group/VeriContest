use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        1 <= k <= (nums.len() as int + 1) / 2,
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000000000,
        1 <= result.1 <= (result.0.len() as int + 1) / 2,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set first element to 1 (min value boundary)
        let mut n = nums;
        n.set(0, 1);
        (n, k)
    } else if mutation_kind == 2 {
        // set first element to max value boundary
        let mut n = nums;
        n.set(0, 1_000_000_000);
        (n, k)
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 1);
        (n, k)
    } else if mutation_kind == 4 {
        // set last element to max
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 1_000_000_000);
        (n, k)
    } else if mutation_kind == 5 && nums.len() < 100000 {
        // grow by one element (push 1)
        let mut n = nums;
        n.push(1);
        // k is still valid: (n.len()+1)/2 >= (nums.len()+1)/2 >= k
        (n, k)
    } else if mutation_kind == 6 && nums.len() > 1 && (k as usize) <= (nums.len() / 2) {
        // shrink by one element (pop), only if k remains valid
        let mut n = nums;
        n.pop();
        (n, k)
    } else if mutation_kind == 7 {
        // set k to 1 (min k)
        (nums, 1)
    } else if mutation_kind == 8 {
        // set k to max valid value
        let max_k = ((nums.len() + 1) / 2) as i32;
        (nums, max_k)
    } else if mutation_kind == 9 {
        // set all elements to same value (first element)
        let val = nums[0];
        let mut n = nums;
        let mut i: usize = 1;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                1 <= n.len() <= 100000,
                1 <= val <= 1000000000,
                forall|j: int| 0 <= j < i ==> n[j] == val,
                forall|j: int| i <= j < n.len() ==> n[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] n[j] <= 1000000000,
                forall|j: int| i <= j < n.len() ==> 1 <= #[trigger] n[j] <= 1000000000,
            decreases n.len() - i,
        {
            n.set(i, val);
            i += 1;
        }
        (n, k)
    } else if mutation_kind == 10 && nums.len() >= 2 {
        // swap first and last elements
        let mut n = nums;
        let last = n.len() - 1;
        let first_val = n[0];
        let last_val = n[last];
        n.set(0, last_val);
        n.set(last, first_val);
        (n, k)
    } else if mutation_kind == 11 {
        // nudge first element up (if possible)
        let mut n = nums;
        if n[0] < 1_000_000_000 {
            n.set(0, n[0] + 1);
        }
        (n, k)
    } else if mutation_kind == 12 {
        // nudge first element down (if possible)
        let mut n = nums;
        if n[0] > 1 {
            n.set(0, n[0] - 1);
        }
        (n, k)
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
        nums.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    nums
}

fn random_k(rng: &mut Rng, n: usize) -> i32 {
    let max_k = (n + 1) / 2;
    rng.gen_range_usize(1, max_k) as i32
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2560);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?},{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_capability(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from problem description
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![2, 3, 5, 9], 2),
        (vec![2, 7, 9, 3, 1], 2),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seed inputs with diverse characteristics
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),                                       // min length
        (vec![1_000_000_000], 1),                           // max value single
        (vec![1, 1], 1),                                    // all same, min value
        (vec![1_000_000_000, 1_000_000_000], 1),            // all same, max value
        (vec![1, 2, 3, 4, 5], 3),                           // ascending, max k
        (vec![5, 4, 3, 2, 1], 3),                           // descending, max k
        (vec![1, 1_000_000_000, 1, 1_000_000_000, 1], 3),  // alternating extremes
        (vec![5, 1, 5, 1, 5], 2),                           // alternating
        (vec![3, 3, 3, 3, 3, 3], 3),                        // all same
        (vec![1, 2], 1),                                    // two elements, k=1
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    // Apply every mutation to every seed
    for (nums, k) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = mutate(nums.clone(), *k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes for random generation
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),         // tiny
        (6, 20),        // small
        (21, 100),      // medium
        (101, 1000),    // large
        (1001, 10000),  // very large
    ];

    // Random seeds with random mutations across size classes
    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            if count >= count_target { break; }
            let len = rng.gen_range_usize(*lo, *hi);
            let nums = random_nums(&mut rng, len);
            let k = random_k(&mut rng, len);
            let mk = rng.gen_range_usize(0, 12) as u8;
            let (result_nums, result_k) = mutate(nums, k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random inputs, identity mutation
    while count < count_target {
        let class = rng.gen_range_usize(0, 4);
        let (lo, hi) = size_classes[class];
        let len = rng.gen_range_usize(lo, hi);
        let nums = random_nums(&mut rng, len);
        let k = random_k(&mut rng, len);
        let (result_nums, result_k) = mutate(nums, k, 0);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
