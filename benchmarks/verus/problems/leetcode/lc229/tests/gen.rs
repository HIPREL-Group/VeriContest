use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 50_000,
        forall|i: int| 0 <= i < nums.len()
            ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 50_000,
        forall|i: int| 0 <= i < result.len()
            ==> -1_000_000_000 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to max boundary
        let mut d = nums;
        d.set(0, 1_000_000_000);
        d
    } else if mutation_kind == 2 {
        // set first element to min boundary
        let mut d = nums;
        d.set(0, -1_000_000_000);
        d
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 4 {
        // set all elements to the first element (guaranteed majority)
        let mut d = nums;
        let val = d[0];
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                -1_000_000_000 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < nums.len()
                    ==> -1_000_000_000 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && nums.len() < 50_000 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        assert(d.len() <= 50_000);
        assert(forall|j: int| 0 <= j < d.len() - 1
            ==> -1_000_000_000 <= #[trigger] d[j] <= 1_000_000_000);
        assert(-1_000_000_000 <= d[d.len() as int - 1] <= 1_000_000_000);
        d
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 8 {
        // nudge last element up (if below max)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1_000_000_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 9 {
        // nudge last element down (if above min)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > -1_000_000_000 {
            d.set(last, d[last] - 1);
        }
        d
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32);
    }
    nums
}

/// Build an array where `val` appears more than n/3 times.
fn nums_with_majority(rng: &mut Rng, len: usize, val: i32) -> Vec<i32> {
    let majority_count = len / 3 + 1;
    let mut nums = Vec::with_capacity(len);
    for i in 0..len {
        if i < majority_count {
            nums.push(val);
        } else {
            nums.push(rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32);
        }
    }
    // Shuffle by doing a bunch of swaps
    for _ in 0..len {
        let a = rng.gen_range_usize(0, len - 1);
        let b = rng.gen_range_usize(0, len - 1);
        nums.swap(a, b);
    }
    nums
}

/// Build an array with two majority elements.
fn nums_with_two_majorities(rng: &mut Rng, len: usize, val1: i32, val2: i32) -> Vec<i32> {
    let majority_count = len / 3 + 1;
    let mut nums = Vec::with_capacity(len);
    for i in 0..len {
        if i < majority_count {
            nums.push(val1);
        } else if i < 2 * majority_count && i < len {
            nums.push(val2);
        } else {
            nums.push(rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32);
        }
    }
    for _ in 0..len {
        let a = rng.gen_range_usize(0, len - 1);
        let b = rng.gen_range_usize(0, len - 1);
        nums.swap(a, b);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(229);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::majority_element(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 2, 3],
        vec![1],
        vec![1, 2],
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted seeds: single majority, two majorities, no majority, boundary values
    let hand_crafted: Vec<Vec<i32>> = vec![
        vec![1, 1, 1, 2, 3],                          // 1 is majority
        vec![1, 1, 2, 2, 3],                           // 1 and 2 are majorities
        vec![1, 2, 3, 4, 5],                           // no majority
        vec![1_000_000_000],                            // max boundary single
        vec![-1_000_000_000],                           // min boundary single
        vec![0, 0, 0, 0],                              // all zeros
        vec![-1, -1, -1, 2, 3],                        // negative majority
        vec![1_000_000_000, 1_000_000_000, -1_000_000_000], // boundary majority
    ];

    for hc in &hand_crafted {
        for &mk in &mutation_kinds {
            let result = mutate(hc.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with majority elements (diverse sizes)
    for _ in 0..15 {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };
        let val = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        let nums = nums_with_majority(&mut rng, n, val);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Random arrays with two majority elements
    for _ in 0..10 {
        let n = match rng.gen_range_usize(0, 3) {
            0 => rng.gen_range_usize(2, 10),
            1 => rng.gen_range_usize(11, 100),
            _ => rng.gen_range_usize(101, 500),
        };
        let v1 = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        let v2 = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        let nums = nums_with_two_majorities(&mut rng, n, v1, v2);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Fully random arrays (no guaranteed majority)
    while count < target_count {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }
}
