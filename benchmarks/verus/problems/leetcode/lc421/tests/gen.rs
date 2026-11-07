use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 200_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX,
    ensures
        1 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= i32::MAX,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut v = nums;
        v.set(0, 0);
        v
    } else if mutation_kind == 2 {
        // set first element to i32::MAX
        let mut v = nums;
        v.set(0, i32::MAX);
        v
    } else if mutation_kind == 3 && nums.len() < 200_000 {
        // grow: push 0
        let mut v = nums;
        v.push(0);
        v
    } else if mutation_kind == 4 && nums.len() > 1 {
        // shrink: pop last element
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> v[j] == 0,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        v
    } else if mutation_kind == 6 {
        // set last element to i32::MAX
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, i32::MAX);
        v
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first two elements
        let mut v = nums;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        v
    } else if mutation_kind == 8 {
        // nudge first element up (if < i32::MAX)
        let mut v = nums;
        if v[0] < i32::MAX {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 9 {
        // nudge first element down (if > 0)
        let mut v = nums;
        if v[0] > 0 {
            v.set(0, v[0] - 1);
        }
        v
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
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, i32::MAX as i64) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(421);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", nums);
        if *count >= target || !seen.insert(key) {
            return;
        }
        let output = Solution::find_maximum_xor(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Hand-picked seeds for edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![0, 0],
        vec![i32::MAX],
        vec![3, 10, 5, 25, 2, 8],
        vec![14, 70, 53, 83, 49, 91, 36, 80, 92, 51, 66, 70],
        vec![1, 2, 4, 8, 16, 32],
        vec![0, i32::MAX],
        vec![1, 1, 1, 1],
        vec![0, 1, 2, 3, 4, 5],
        vec![i32::MAX, i32::MAX - 1],
        vec![1024, 512, 256, 128, 64],
        vec![7, 7, 7],
        vec![0, 0, 0, 0, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with size classes
    for i in 0..60 {
        let n = match i % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 20),       // small
            2 => rng.gen_range_usize(10, 100),     // medium
            3 => rng.gen_range_usize(50, 500),     // large
            _ => rng.gen_range_usize(100, 1000),   // larger
        };
        let seed = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds
    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let seed = random_nums(&mut rng, n);
        emit(mutate(seed, 0), &mut seen, &mut out, &mut count);
    }
}
