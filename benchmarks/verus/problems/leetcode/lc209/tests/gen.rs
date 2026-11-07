use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elements: &Vec<i32>,
    target: i32,
    mutation_kind: u8,
) -> (result: (i32, Vec<i32>))
    requires
        1 <= elements.len() <= 100_000,
        forall|i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 10_000,
        1 <= target <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1.len() <= 100_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 10_000,
{
    if mutation_kind == 0 {
        let nums = elements.clone();
        (target, nums)
    } else if mutation_kind == 1 {
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < elements.len()
            invariant
                0 <= i <= elements.len(),
                nums.len() == i,
                1 <= elements.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> #[trigger] nums[j] == 1i32,
            decreases elements.len() - i,
        {
            nums.push(1);
            i += 1;
        }
        assert(nums.len() == elements.len());
        (target, nums)
    } else if mutation_kind == 2 {
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < elements.len()
            invariant
                0 <= i <= elements.len(),
                nums.len() == i,
                1 <= elements.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> #[trigger] nums[j] == 10_000i32,
            decreases elements.len() - i,
        {
            nums.push(10_000);
            i += 1;
        }
        assert(nums.len() == elements.len());
        (target, nums)
    } else if mutation_kind == 3 && elements.len() > 1 {
        let mut nums = elements.clone();
        nums.pop();
        assert(nums.len() >= 1);
        (target, nums)
    } else if mutation_kind == 4 && elements.len() < 100_000 {
        let mut nums = elements.clone();
        nums.push(1);
        assert(nums.len() <= 100_000);
        assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 10_000 by {
            if i < elements.len() as int {
                assert(1 <= elements[i] <= 10_000);
            }
        }
        (target, nums)
    } else if mutation_kind == 5 {
        let mut nums = elements.clone();
        nums.set(0, 1);
        assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 10_000 by {
            if i == 0 {
                assert(nums[0] == 1);
            } else {
                assert(nums[i] == elements[i]);
            }
        }
        (target, nums)
    } else if mutation_kind == 6 {
        let mut nums = elements.clone();
        nums.set(0, 10_000);
        assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 10_000 by {
            if i == 0 {
                assert(nums[0] == 10_000);
            } else {
                assert(nums[i] == elements[i]);
            }
        }
        (target, nums)
    } else if mutation_kind == 7 && target < 1_000_000_000 {
        let nums = elements.clone();
        (target + 1, nums)
    } else if mutation_kind == 8 && target > 1 {
        let nums = elements.clone();
        (target - 1, nums)
    } else if mutation_kind == 9 {
        let nums = elements.clone();
        (1, nums)
    } else if mutation_kind == 10 {
        let nums = elements.clone();
        (1_000_000_000, nums)
    } else if mutation_kind == 11 && elements.len() >= 2 {
        let mut nums = elements.clone();
        let a = nums[0];
        let b = nums[1];
        nums.set(0, b);
        nums.set(1, a);
        assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 10_000 by {
            if i == 0 {
                assert(nums[0] == b);
                assert(1 <= b <= 10_000);
            } else if i == 1 {
                assert(nums[1] == a);
                assert(1 <= a <= 10_000);
            } else {
                assert(nums[i] == elements[i]);
            }
        }
        (target, nums)
    } else {
        let nums = elements.clone();
        (target, nums)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 10_000) as i32);
    }
    nums
}

fn mutate(elements: Vec<i32>, target: i32, mutation_kind: u8) -> (i32, Vec<i32>) {
    generate_test_case(&elements, target, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(209);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, target: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}:{}", nums, target);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_sub_array_len(target, nums.clone());
        writeln!(out, "{}", json!({"input": {"target": target, "nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    emit(vec![2, 3, 1, 2, 4, 3], 7, &mut seen, &mut out, &mut count);
    emit(vec![1, 4, 4], 4, &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1, 1, 1, 1, 1], 11, &mut seen, &mut out, &mut count);

    // Boundary seeds
    let boundary_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1], 1_000_000_000),
        (vec![10_000], 1),
        (vec![10_000], 10_000),
        (vec![1, 1], 2),
        (vec![10_000, 10_000], 1),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply mutations to boundary seeds
    for (seed_nums, seed_target) in &boundary_seeds {
        for &mk in &mutation_kinds {
            let (target, nums) = mutate(seed_nums.clone(), *seed_target, mk);
            emit(nums, target, &mut seen, &mut out, &mut count);
        }
    }

    // Diverse random cases with size classes
    while count < count_target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10_000),
        };

        let target = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_i64(1, 100) as i32,
            2 => rng.gen_range_i64(100, 100_000) as i32,
            _ => rng.gen_range_i64(100_000, 1_000_000_000) as i32,
        };

        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (result_target, result_nums) = mutate(nums, target, mk);
        emit(result_nums, result_target, &mut seen, &mut out, &mut count);
    }
}
