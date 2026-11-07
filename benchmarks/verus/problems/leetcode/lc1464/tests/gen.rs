use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    // Construction parameters: a base array of valid values and a mutation selector
    nums: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 500,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    ensures
        2 <= result.len() <= 500,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity — return as-is
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum boundary)
        let mut h = nums;
        let last = h.len() - 1;
        h.set(last, 1);
        h
    } else if mutation_kind == 2 {
        // set last element to 1000 (maximum boundary)
        let mut h = nums;
        let last = h.len() - 1;
        h.set(last, 1000);
        h
    } else if mutation_kind == 3 {
        // set first element to 1 (minimum boundary)
        let mut h = nums;
        h.set(0, 1);
        h
    } else if mutation_kind == 4 {
        // set all elements to same value (500)
        let mut h = nums;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == nums.len(),
                2 <= h.len() <= 500,
                forall |j: int| 0 <= j < i ==> h[j] == 500int,
                forall |j: int| i <= j < h.len() ==> h[j] == nums[j],
            decreases h.len() - i,
        {
            h.set(i, 500);
            i += 1;
        }
        h
    } else if mutation_kind == 5 && nums.len() < 500 {
        // grow by one element (push 500)
        let mut h = nums;
        h.push(500);
        h
    } else if mutation_kind == 6 && nums.len() > 2 {
        // shrink by one element (pop)
        let mut h = nums;
        h.pop();
        h
    } else if mutation_kind == 7 {
        // nudge last element: if < 1000, increment by 1
        let mut h = nums;
        let last = h.len() - 1;
        if h[last] < 1000 {
            h.set(last, h[last] + 1);
        }
        h
    } else if mutation_kind == 8 {
        // nudge first element down: if > 1, decrement by 1
        let mut h = nums;
        if h[0] > 1 {
            h.set(0, h[0] - 1);
        }
        h
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

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_product(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example 1 from description.md
    emit(vec![3, 4, 5, 2], &mut seen, &mut out, &mut count);

    // Example 2 from description.md
    emit(vec![1, 5, 4, 5], &mut seen, &mut out, &mut count);

    // Example 3 from description.md
    emit(vec![3, 7], &mut seen, &mut out, &mut count);

    // Boundary cases
    emit(vec![1, 1], &mut seen, &mut out, &mut count);
    emit(vec![1000, 1000], &mut seen, &mut out, &mut count);
    emit(vec![1, 1000], &mut seen, &mut out, &mut count);

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Generate a helper to build a random valid array
    let gen_nums = |rng: &mut Rng, n: usize| -> Vec<i32> {
        let mut v = Vec::new();
        for _ in 0..n {
            v.push(rng.gen_range_i64(1, 1000) as i32);
        }
        v
    };

    // Size classes for array lengths
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 3),       // tiny
        (4, 10),      // small
        (11, 50),     // medium
        (51, 200),    // large
        (201, 500),   // max
    ];

    // Structured: all mutation kinds on various sizes with boundary values
    for &(lo, hi) in &size_classes {
        for &mk in &mutation_kinds {
            if count >= count_target { break; }
            let n = rng.gen_range_usize(lo, hi);
            let nums = gen_nums(&mut rng, n);
            let result = generate_test_case(nums, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Boundary-value arrays
    let boundary_arrs: Vec<Vec<i32>> = vec![
        vec![1; 2],
        vec![1000; 2],
        vec![1; 500],
        vec![1000; 500],
        vec![1, 1000, 1, 1000],
    ];
    for arr in boundary_arrs {
        for &mk in &mutation_kinds {
            if count >= count_target { break; }
            let result = generate_test_case(arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random generation to fill remaining
    while count < count_target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 3),
            1 => rng.gen_range_usize(4, 15),
            2 => rng.gen_range_usize(16, 100),
            3 => rng.gen_range_usize(101, 300),
            _ => rng.gen_range_usize(301, 500),
        };
        let nums = gen_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = generate_test_case(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
