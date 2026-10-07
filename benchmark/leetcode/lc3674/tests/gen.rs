use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set all elements equal to first element
        let val = nums[0];
        let mut d = nums;
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                1 <= val <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 2 && nums.len() >= 2 {
        // set second element to differ from first (ensure not all equal)
        let mut d = nums;
        let new_val: i32 = if d[0] < 100000 { (d[0] + 1) as i32 } else { 1i32 };
        d.set(1, new_val);
        d
    } else if mutation_kind == 3 {
        // nudge first element up (if < 100000)
        let mut d = nums;
        if d[0] < 100000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 4 {
        // nudge first element down (if > 1)
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 5 {
        // set last element to 1 (boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 6 {
        // set last element to 100000 (boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100000);
        d
    } else if mutation_kind == 7 && nums.len() < 100 {
        // grow by one element (push first element value)
        let val = nums[0];
        let mut d = nums;
        d.push(val);
        d
    } else if mutation_kind == 8 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp = d[0];
        d.set(0, d[last]);
        d.set(last, tmp);
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100000) as i32);
    }
    nums
}

fn all_same(rng: &mut Rng, len: usize) -> Vec<i32> {
    let val = rng.gen_range_i64(1, 100000) as i32;
    vec![val; len]
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3674);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::min_operations(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2],
        vec![5, 5, 5],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Curated seeds: boundary and interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100000],
        vec![1, 1],
        vec![1, 2],
        vec![100000, 100000],
        vec![1, 100000],
        vec![50000, 50000, 50000],
        vec![1, 1, 1, 1, 1],
        vec![1, 2, 3, 4, 5],
        vec![99999, 100000],
        vec![1, 1, 1, 2],
        vec![2, 1, 1, 1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with diverse sizes and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),     // tiny
        (4, 10),    // small
        (11, 30),   // medium
        (31, 70),   // large
        (71, 100),  // max
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..5 {
            let len = rng.gen_range_usize(*lo, *hi);
            let s = random_nums(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            emit(mutate(s, mk), &mut seen, &mut out, &mut count);
        }
    }

    // All-same arrays of various sizes
    for &len in &[1, 2, 5, 10, 50, 100] {
        let s = all_same(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random inputs
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let use_same = rng.gen_range_usize(0, 4) == 0;
        let s = if use_same { all_same(&mut rng, len) } else { random_nums(&mut rng, len) };
        emit(mutate(s, mk), &mut seen, &mut out, &mut count);
    }
}
