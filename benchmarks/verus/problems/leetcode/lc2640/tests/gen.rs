use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000000000,
{
    if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 {
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 2 {
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 3 {
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100000,
                forall|j: int| 0 <= j < i ==> #[trigger] v[j] == 1,
                forall|j: int| i <= j < v.len() ==> #[trigger] v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && nums.len() < 100000 {
        let mut v = nums;
        v.push(1);
        v
    } else if mutation_kind == 5 && nums.len() > 1 {
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 6 {
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] < 1_000_000_000 {
            v.set(last, v[last] + 1);
        }
        v
    } else if mutation_kind == 7 {
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] > 1 {
            v.set(last, v[last] - 1);
        }
        v
    } else if mutation_kind == 8 {
        let mut v = nums;
        v.set(0, 1_000_000_000);
        v
    } else if mutation_kind == 9 {
        let mut v = nums;
        v.set(0, 1);
        v
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
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(2640);
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
        let output = Solution::find_prefix_score(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    let examples: Vec<Vec<i32>> = vec![
        vec![2, 3, 7, 5, 10],
        vec![1, 1, 2, 4, 8, 16],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for seed in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1_000_000_000],
        vec![1, 1_000_000_000],
        vec![1_000_000_000, 1],
        vec![500_000_000, 500_000_000, 500_000_000],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
    ];

    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    for i in 0..200 {
        if count >= target { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let seed = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let n = rng.gen_range_usize(1, 1000);
        let seed = random_nums(&mut rng, n);
        emit(mutate(seed, 0), &mut seen, &mut out, &mut count);
    }
}
