use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> nums[i] == 0 || nums[i] == 1,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0 || result[i] == 1,
{
    if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 {
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] == 0 {
            d.set(last, 1);
        } else {
            d.set(last, 0);
        }
        d
    } else if mutation_kind == 2 {
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| #![trigger d[j]] i <= j < d.len() ==> d[j] == nums[j],
            decreases (d.len() - i),
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 3 {
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| #![trigger d[j]] i <= j < d.len() ==> d[j] == nums[j],
            decreases (d.len() - i),
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100_000 {
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 5 && nums.len() < 100_000 {
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 6 && nums.len() > 1 {
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 {
        let mut d = nums;
        if d[0] == 0 {
            d.set(0, 1);
        } else {
            d.set(0, 0);
        }
        d
    } else if mutation_kind == 8 && nums.len() >= 2 {
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else {
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_range_u8(&mut self, lo: u8, hi: u8) -> u8 {
        assert!(lo <= hi);
        lo + (self.next_u64() as u8) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_binary_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_usize(0, 1) as i32);
    }
    arr
}

extern crate serde_json;
use serde_json::json;

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
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::longest_subarray(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 1, 0, 1],
        vec![0, 1, 1, 1, 0, 1, 1, 0, 1],
        vec![1, 1, 1],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Edge-case seeds
    let edge_seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![0, 0],
        vec![1, 0],
        vec![0, 1],
        vec![1, 1],
        vec![0, 0, 0],
        vec![1, 0, 1],
        vec![1, 1, 1, 1, 1],
        vec![0, 0, 0, 0, 0],
        vec![1, 0, 0, 0, 1],
    ];
    for s in &edge_seeds {
        for mk in 0..=8u8 {
            emit(generate_test_case(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    while count < target {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let arr = random_binary_array(&mut rng, n);
        let mk = rng.gen_range_u8(0, 8);
        emit(generate_test_case(arr, mk), &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
