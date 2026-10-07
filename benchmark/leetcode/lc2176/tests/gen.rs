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
        // set all elements to the same value (creates many equal pairs)
        let val = nums[0];
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                1 <= val <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 100,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 2 && nums.len() < 100 {
        // grow: push a copy of the first element
        let val = nums[0];
        let mut d = nums;
        d.push(val);
        (d, k)
    } else if mutation_kind == 3 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 4 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        (d, k)
    } else if mutation_kind == 5 {
        // set k to 1 (every product divisible by 1)
        (nums, 1)
    } else if mutation_kind == 6 {
        // set k to 100 (max boundary)
        (nums, 100)
    } else if mutation_kind == 7 {
        // nudge first element: if < 100, increment by 1
        let mut d = nums;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        (d, k)
    } else if mutation_kind == 8 {
        // set first element to 1 (min boundary)
        let mut d = nums;
        d.set(0, 1);
        (d, k)
    } else if mutation_kind == 9 {
        // set first element to 100 (max boundary)
        let mut d = nums;
        d.set(0, 100);
        (d, k)
    } else if mutation_kind == 10 {
        // duplicate first element at last position (create a matching pair)
        let val = nums[0];
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, val);
        (d, k)
    } else {
        // fallback
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2176);
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
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_pairs(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![3,1,2,2,2,1,3], 2, &mut seen, &mut out, &mut count);
    emit(vec![1,2,3,4], 1, &mut seen, &mut out, &mut count);

    // Hand-crafted seeds for diversity
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1, 1], 1),
        (vec![1, 1], 2),
        (vec![100, 100], 100),
        (vec![1, 1, 1, 1, 1], 1),
        (vec![5, 5, 5, 5, 5], 3),
        (vec![1, 2, 1, 2, 1], 2),
        (vec![50, 50, 50], 50),
        (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 5),
        (vec![100], 100),
        (vec![42, 42, 42, 42], 7),
        (vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 10),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed
    for (s_nums, s_k) in &seeds {
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = mutate(s_nums.clone(), *s_k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds × random mutations across size classes
    for i in 0..80 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),     // tiny
            1 => rng.gen_range_usize(1, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };
        let k = rng.gen_range_i64(1, 100) as i32;
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (result_nums, result_k) = mutate(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutations
    while count < target_count {
        let len = rng.gen_range_usize(1, 100);
        let k = rng.gen_range_i64(1, 100) as i32;
        let nums = random_nums(&mut rng, len);
        let (result_nums, result_k) = mutate(nums, k, 0);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
