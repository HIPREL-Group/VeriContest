use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 2000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
    ensures
        2 <= result.len() <= 2000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 0);
        v
    } else if mutation_kind == 2 {
        // set all elements to the same value (first element)
        let val = nums[0];
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                2 <= v.len() <= 2000,
                0 <= val <= 1000,
                forall|j: int| 0 <= j < i ==> v[j] == val,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, val);
            i += 1;
        }
        v
    } else if mutation_kind == 3 && nums.len() < 2000 {
        // grow by one element (push 0)
        let mut v = nums;
        v.push(0);
        v
    } else if mutation_kind == 4 && nums.len() > 2 {
        // shrink by one element (pop)
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 5 {
        // set first two elements equal (triggers the doubling operation)
        let val = nums[0];
        let mut v = nums;
        v.set(1, val);
        v
    } else if mutation_kind == 6 {
        // nudge first element up: if < 1000, increment by 1
        let mut v = nums;
        if v[0] < 1000 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 7 {
        // nudge first element down: if > 0, decrement by 1
        let mut v = nums;
        if v[0] > 0 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 8 {
        // set all elements to 0
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                2 <= v.len() <= 2000,
                forall|j: int| 0 <= j < i ==> v[j] == 0i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        v
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first two elements
        let a = nums[0];
        let b = nums[1];
        let mut v = nums;
        v.set(0, b);
        v.set(1, a);
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 1000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2460);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", nums);
        if *count >= target || !seen.insert(key) {
            return;
        }
        let output = Solution::apply_operations(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 2, 2, 1, 1, 0],
        vec![0, 1],
        // Boundary and interesting cases
        vec![0, 0],
        vec![1000, 1000],
        vec![500, 500, 500, 500],
        vec![0, 0, 0, 0, 0],
        vec![1, 1, 1, 1, 1, 1],
        vec![1, 0],
        vec![999, 999],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![0, 1, 0, 1, 0, 1],
        vec![7, 7, 7, 7],
        vec![1000, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    for i in 0..80 {
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(2, 5),     // tiny
            1 => rng.gen_range_usize(2, 10),    // small
            2 => rng.gen_range_usize(11, 100),  // medium
            3 => rng.gen_range_usize(101, 500), // large
            _ => rng.gen_range_usize(501, 2000), // max
        };
        let seed = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let n = rng.gen_range_usize(2, 2000);
        let seed = random_nums(&mut rng, n);
        emit(mutate(seed, 0), &mut seen, &mut out, &mut count);
    }
}
