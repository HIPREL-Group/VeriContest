use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    index_difference: i32,
    value_difference: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= nums.len() <= 100,
        0 <= index_difference <= 100,
        0 <= value_difference <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50,
    ensures
        1 <= result.0.len() <= 100,
        0 <= result.1 <= 100,
        0 <= result.2 <= 50,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 50,
{
    if mutation_kind == 0 {
        (nums, index_difference, value_difference)
    } else if mutation_kind == 1 {
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, index_difference, value_difference)
    } else if mutation_kind == 2 {
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 50,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 50);
            i += 1;
        }
        (d, index_difference, value_difference)
    } else if mutation_kind == 3 && nums.len() < 100 {
        let mut d = nums;
        d.push(0);
        (d, index_difference, value_difference)
    } else if mutation_kind == 4 && nums.len() > 1 {
        let mut d = nums;
        d.pop();
        (d, index_difference, value_difference)
    } else if mutation_kind == 5 {
        let mut d = nums;
        d.set(0, 0);
        (d, index_difference, value_difference)
    } else if mutation_kind == 6 {
        let mut d = nums;
        d.set(0, 50);
        (d, index_difference, value_difference)
    } else if mutation_kind == 7 {
        (nums, 0, value_difference)
    } else if mutation_kind == 8 {
        (nums, index_difference, 0)
    } else if mutation_kind == 9 {
        (nums, 100, value_difference)
    } else if mutation_kind == 10 {
        (nums, index_difference, 50)
    } else if mutation_kind == 11 {
        (nums, 0, 0)
    } else if mutation_kind == 12 {
        if nums.len() >= 2 {
            let mut d = nums;
            let last = d.len() - 1;
            let tmp_first = d[0];
            let tmp_last = d[last];
            d.set(0, tmp_last);
            d.set(last, tmp_first);
            (d, index_difference, value_difference)
        } else {
            (nums, index_difference, value_difference)
        }
    } else if mutation_kind == 13 && index_difference > 0 {
        (nums, index_difference - 1, value_difference)
    } else if mutation_kind == 14 && value_difference > 0 {
        (nums, index_difference, value_difference - 1)
    } else if mutation_kind == 15 && index_difference < 100 {
        (nums, index_difference + 1, value_difference)
    } else if mutation_kind == 16 && value_difference < 50 {
        (nums, index_difference, value_difference + 1)
    } else {
        (nums, index_difference, value_difference)
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

fn mutate(nums: Vec<i32>, index_difference: i32, value_difference: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_test_case(nums, index_difference, value_difference, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 50) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2903);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, idx_diff: i32, val_diff: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}_{}", nums, idx_diff, val_diff);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::find_indices(nums.clone(), idx_diff, val_diff);
        writeln!(out, "{}", json!({
            "input": {
                "nums": nums,
                "indexDifference": idx_diff,
                "valueDifference": val_diff
            },
            "output": output
        })).unwrap();
        *count += 1;
    };

    let examples: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![5, 1, 4, 1], 2, 4),
        (vec![2, 1], 0, 0),
        (vec![1, 2, 3], 2, 4),
    ];
    for (nums, id, vd) in &examples {
        emit(nums.clone(), *id, *vd, &mut seen, &mut out, &mut count);
    }

    let seed_nums: Vec<Vec<i32>> = vec![
        vec![0],
        vec![50],
        vec![0, 50],
        vec![50, 0],
        vec![25, 25, 25],
        vec![0, 0, 0, 0, 0],
        vec![50, 50, 50, 50, 50],
        vec![0, 10, 20, 30, 40, 50],
        vec![50, 40, 30, 20, 10, 0],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    ];

    let idx_diffs: Vec<i32> = vec![0, 1, 2, 5, 10, 50, 100];
    let val_diffs: Vec<i32> = vec![0, 1, 5, 10, 25, 50];
    let mutation_kinds: Vec<u8> = (0..=16).collect();

    for nums in &seed_nums {
        for &id in &idx_diffs {
            for &vd in &val_diffs {
                for &mk in &mutation_kinds {
                    if count >= target { break; }
                    let (rn, ri, rv) = mutate(nums.clone(), id, vd, mk);
                    emit(rn, ri, rv, &mut seen, &mut out, &mut count);
                }
            }
        }
    }

    while count < target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let nums = random_nums(&mut rng, len);
        let id = rng.gen_range_i64(0, 100) as i32;
        let vd = rng.gen_range_i64(0, 50) as i32;
        let mk = rng.gen_range_usize(0, 16) as u8;
        let (rn, ri, rv) = mutate(nums, id, vd, mk);
        emit(rn, ri, rv, &mut seen, &mut out, &mut count);
    }
}
