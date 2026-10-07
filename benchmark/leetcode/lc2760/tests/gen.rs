use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, threshold: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100,
        1 <= threshold <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        1 <= result.1 <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        (nums, threshold)
    } else if mutation_kind == 1 {
        // set last element to an even value (2) to encourage alternating start
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 2);
        (d, threshold)
    } else if mutation_kind == 2 {
        // set first element to an even value (2)
        let mut d = nums;
        d.set(0, 2);
        (d, threshold)
    } else if mutation_kind == 3 {
        // set all elements to threshold (all equal, no alternation beyond first even)
        let t = threshold;
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                1 <= t <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == t,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, t);
            i += 1;
        }
        (d, threshold)
    } else if mutation_kind == 4 {
        // build perfect alternating pattern: even, odd, even, odd, ...
        // uses values 2 and 3 which are both <= 100
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> (
                    if j % 2 == 0 { d[j] == 2 } else { d[j] == 3 }
                ),
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] d[j] <= 100,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            if i % 2 == 0 {
                d.set(i, 2);
            } else {
                d.set(i, 3);
            }
            i += 1;
        }
        (d, threshold)
    } else if mutation_kind == 5 && nums.len() < 100 {
        // grow: push element 1
        let mut d = nums;
        d.push(1);
        (d, threshold)
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        (d, threshold)
    } else if mutation_kind == 7 {
        // set threshold to 1 (minimum threshold)
        (nums, 1)
    } else if mutation_kind == 8 {
        // set threshold to 100 (maximum threshold)
        (nums, 100)
    } else if mutation_kind == 9 {
        // nudge first element: if < 100, increment
        let mut d = nums;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        (d, threshold)
    } else if mutation_kind == 10 {
        // set first element to 1 (odd, so no alternating subarray starts here)
        let mut d = nums;
        d.set(0, 1);
        (d, threshold)
    } else if mutation_kind == 11 {
        // swap first two elements if length >= 2
        if nums.len() >= 2 {
            let mut d = nums;
            let a = d[0];
            let b = d[1];
            d.set(0, b);
            d.set(1, a);
            (d, threshold)
        } else {
            (nums, threshold)
        }
    } else {
        // fallback: identity
        (nums, threshold)
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

fn mutate(nums: Vec<i32>, threshold: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, threshold, mutation_kind)
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2760);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, threshold: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", nums, threshold);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::longest_alternating_subarray(nums.clone(), threshold);
        writeln!(out, "{}", json!({"input": {"nums": nums, "threshold": threshold}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![3, 2, 5, 4], 5),
        (vec![1, 2], 2),
        (vec![2, 3, 4, 5], 4),
    ];
    for (nums, threshold) in examples {
        emit(nums, threshold, &mut seen, &mut out, &mut count);
    }

    // Curated seeds for diversity
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),                             // single odd element
        (vec![2], 2),                             // single even element
        (vec![2, 3], 3),                          // perfect pair
        (vec![2, 3, 4, 5, 6], 10),                // perfect alternating
        (vec![1, 1, 1, 1], 5),                    // all odd
        (vec![2, 2, 2, 2], 5),                    // all even (no alternation)
        (vec![100, 99, 98, 97], 100),             // large values at threshold
        (vec![1, 2, 3, 4, 5, 6, 7, 8], 4),       // threshold cuts off some elements
        (vec![50, 51, 50, 51, 50], 51),           // alternating near threshold
        (vec![2, 1, 2, 1, 2, 1, 2, 1, 2, 1], 2), // alternating at min threshold
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every curated seed
    for (nums, threshold) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (result_nums, result_threshold) = mutate(nums.clone(), *threshold, mk);
            emit(result_nums, result_threshold, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with random mutations
    for _ in 0..200 {
        if count >= target { break; }
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 100),    // large
            _ => rng.gen_range_usize(1, 100),     // any
        };
        let nums = random_nums(&mut rng, len);
        let threshold = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (result_nums, result_threshold) = mutate(nums, threshold, mk);
        emit(result_nums, result_threshold, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutation on random inputs
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let nums = random_nums(&mut rng, len);
        let threshold = rng.gen_range_i64(1, 100) as i32;
        let (result_nums, result_threshold) = mutate(nums, threshold, 0);
        emit(result_nums, result_threshold, &mut seen, &mut out, &mut count);
    }
}
