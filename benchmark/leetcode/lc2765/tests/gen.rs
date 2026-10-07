use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
    ensures
        2 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 2 {
        // set last element to 10_000 (max boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 10_000);
        v
    } else if mutation_kind == 3 && nums.len() < 100 {
        // grow by one element
        let mut v = nums;
        v.push(1);
        v
    } else if mutation_kind == 4 && nums.len() > 2 {
        // shrink by one element
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 5 {
        // set all elements to the same value (no alternating subarray)
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                2 <= v.len() <= 100,
                forall|j: int| 0 <= j < i ==> v[j] == 5,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 5);
            i += 1;
        }
        v
    } else if mutation_kind == 6 {
        // nudge last element up (if < 10_000)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] < 10_000 {
            v.set(last, v[last] + 1);
        }
        v
    } else if mutation_kind == 7 {
        // nudge last element down (if > 1)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] > 1 {
            v.set(last, v[last] - 1);
        }
        v
    } else if mutation_kind == 8 {
        // swap first two elements
        let mut v = nums;
        let tmp = v[0];
        v.set(0, v[1]);
        v.set(1, tmp);
        v
    } else if mutation_kind == 9 {
        // make first two elements consecutive (force alternating start)
        let mut v = nums;
        if v[0] < 10_000 {
            v.set(1, v[0] + 1);
        } else if v[1] > 1 {
            v.set(0, v[1] - 1);
        }
        v
    } else {
        nums // fallback
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 10_000) as i32);
    }
    v
}

fn alternating_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let base = rng.gen_range_i64(1, 9_999) as i32;
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        if i % 2 == 0 { v.push(base); } else { v.push(base + 1); }
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
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
        let output = Solution::alternating_subarray(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 3, 4, 3, 4],
        vec![4, 5, 6],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Curated seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![1, 2],
        vec![1, 2, 1],
        vec![1, 2, 1, 2, 1],
        vec![10_000, 10_000],
        vec![9_999, 10_000],
        vec![9_999, 10_000, 9_999, 10_000],
        vec![5, 5, 5, 5, 5],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 2, 1, 3, 4, 3, 4, 3],
        vec![100, 101, 100, 101, 100, 101],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Alternating pattern arrays of various sizes
    let size_classes: Vec<usize> = vec![2, 3, 5, 10, 20, 50, 100];
    for &sz in &size_classes {
        let arr = alternating_nums(&mut rng, sz);
        for &mk in &[0u8, 1, 5, 6, 8, 9] {
            let result = mutate(arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with random mutations
    while count < target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 2,                                      // min
            1 => rng.gen_range_usize(2, 5),              // tiny
            2 => rng.gen_range_usize(6, 20),             // small
            3 => rng.gen_range_usize(21, 60),            // medium
            _ => rng.gen_range_usize(61, 100),           // large/max
        };
        let arr = if rng.gen_range_usize(0, 2) == 0 {
            alternating_nums(&mut rng, len)
        } else {
            random_nums(&mut rng, len)
        };
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
