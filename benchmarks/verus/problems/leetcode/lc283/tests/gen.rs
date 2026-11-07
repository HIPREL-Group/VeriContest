use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: &mut Vec<i32>, mutation_kind: u8)
    requires
        1 <= (*old(nums)).len() <= 10_000,
        forall|i: int| 0 <= i < (*old(nums)).len() ==>
            i32::MIN <= #[trigger] (*old(nums))[i] <= i32::MAX,
    ensures
        1 <= (*old(nums)).len() <= 10_000,
        forall|i: int| 0 <= i < (*old(nums)).len() ==>
            i32::MIN <= #[trigger] (*old(nums))[i] <= i32::MAX,
{
    // The ensures refer only to old(nums), which is trivially preserved.
    // The function mutates nums in place for test generation.
    let ghost old_nums = *old(nums);

    if mutation_kind == 1 {
        let last = nums.len() - 1;
        nums.set(last, 0);
    } else if mutation_kind == 2 {
        nums.set(0, 0);
    } else if mutation_kind == 3 {
        let mut i: usize = 0;
        let ghost orig = *nums;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == old_nums.len(),
                1 <= nums.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> nums[j] == 0i32,
                forall|j: int| i <= j < nums.len() ==> nums[j] == orig[j],
            decreases nums.len() - i,
        {
            nums.set(i, 0);
            i += 1;
        }
    } else if mutation_kind == 4 && nums.len() < 10_000 {
        nums.push(0);
    } else if mutation_kind == 5 && nums.len() > 1 {
        nums.pop();
    } else if mutation_kind == 6 && nums.len() >= 2 {
        let a = nums[0];
        let b = nums[1];
        nums.set(0, b);
        nums.set(1, a);
    } else if mutation_kind == 7 {
        nums.set(0, 1);
    } else if mutation_kind == 8 {
        let v = nums[0];
        if v > i32::MIN {
            nums.set(0, -v);
        }
    } else if mutation_kind == 9 {
        let mut i: usize = 0;
        let ghost orig = *nums;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == old_nums.len(),
                1 <= nums.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> nums[j] == 1i32,
                forall|j: int| i <= j < nums.len() ==> nums[j] == orig[j],
            decreases nums.len() - i,
        {
            nums.set(i, 1);
            i += 1;
        }
    }
    // mutation_kind == 0 or fallback: identity (no mutation)
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

fn mutate(mut nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(&mut nums, mutation_kind);
    nums
}

fn random_array_with_zeros(rng: &mut Rng, len: usize, zero_frac: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        if rng.gen_range_usize(0, 99) < zero_frac {
            arr.push(0);
        } else {
            let v = rng.gen_range_i64(-1_000_000, 1_000_000) as i32;
            if v == 0 { arr.push(1); } else { arr.push(v); }
        }
    }
    arr
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(283);
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
        let input_clone = nums.clone();
        let mut nums_mut = nums;
        Solution::move_zeroes(&mut nums_mut);
        writeln!(out, "{}", json!({"input": {"nums": input_clone}, "output": nums_mut})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![0, 1, 0, 3, 12],
        vec![0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to example seeds
    for seed in &example_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted interesting seeds
    let interesting_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![0, 0, 0, 0],
        vec![1, 2, 3, 4, 5],
        vec![0, 0, 0, 1],
        vec![1, 0, 0, 0],
        vec![1, 0, 2, 0, 3, 0],
        vec![0, 1, 0, 2, 0, 3],
        vec![-1, 0, 1, 0, -1],
        vec![i32::MAX, 0, i32::MIN + 1],
        vec![0, 0, 1, 2, 3, 0, 0],
    ];

    for seed in &interesting_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with diverse sizes and zero fractions
    while count < target {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };

        let zero_frac = match count % 4 {
            0 => 0,
            1 => 30,
            2 => 50,
            _ => 80,
        };

        let seed_arr = random_array_with_zeros(&mut rng, n, zero_frac);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
