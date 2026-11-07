use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
    ensures
        2 <= result.len() <= 100,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() > 2 {
        // shrink: remove last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        proof {
            assert forall |i: int, j: int| 0 <= i < j < d@.len()
                implies d@[i] != d@[j] by {
                if i == 0 && j == last as int {
                    assert(d@[i] == nums@[last as int]);
                    assert(d@[j] == nums@[0]);
                } else if i == 0 {
                    assert(d@[i] == nums@[last as int]);
                    assert(d@[j] == nums@[j]);
                } else if j == last as int {
                    assert(d@[i] == nums@[i]);
                    assert(d@[j] == nums@[0]);
                } else {
                    assert(d@[i] == nums@[i]);
                    assert(d@[j] == nums@[j]);
                }
            };
        }
        d
    } else if mutation_kind == 3 && nums.len() > 2 {
        // shrink from front: swap first to last, then pop
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        proof {
            assert forall |i: int, j: int| 0 <= i < j < d@.len()
                implies d@[i] != d@[j] by {
                if i == 0 && j == last as int {
                    assert(d@[i] == nums@[last as int]);
                    assert(d@[j] == nums@[0]);
                } else if i == 0 {
                    assert(d@[i] == nums@[last as int]);
                    assert(d@[j] == nums@[j]);
                } else if j == last as int {
                    assert(d@[i] == nums@[i]);
                    assert(d@[j] == nums@[0]);
                } else {
                    assert(d@[i] == nums@[i]);
                    assert(d@[j] == nums@[j]);
                }
            };
        }
        d.pop();
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

/// Generate a random array of unique values in [1, 100] with the given length.
fn random_unique_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut pool: Vec<i32> = (1..=100).collect();
    // Fisher-Yates shuffle
    for i in (1..pool.len()).rev() {
        let j = rng.gen_range_usize(0, i);
        pool.swap(i, j);
    }
    pool.truncate(len);
    pool
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3731);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::find_missing_elements(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *total += 1;
    };

    // ── Example inputs from description.md ──
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 4, 2, 5],
        vec![7, 8, 6, 9],
        vec![5, 1],
    ];
    for ex in &examples {
        for mk in 0u8..4 {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut total);
        }
    }

    // ── Hand-picked seeds for boundary / edge coverage ──
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 2],                           // min length, min values, no gap
        vec![99, 100],                        // max boundary values, no gap
        vec![1, 100],                         // full range, many gaps
        vec![1, 3],                           // single gap
        vec![50, 51, 52],                     // mid-range consecutive
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], // longer consecutive
        vec![2, 4, 6, 8, 10],                 // all even, gaps
        vec![1, 3, 5, 7, 9],                  // all odd, gaps
        vec![10, 1],                          // descending pair, gaps
        vec![50, 52],                         // single gap mid-range
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3];
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut total);
        }
    }

    // ── Random seeds × random mutations, diverse size classes ──
    while total < count {
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(2, 5),    // tiny
            1 => rng.gen_range_usize(2, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 70),  // large
            _ => rng.gen_range_usize(71, 100), // max
        };
        let arr = random_unique_array(&mut rng, n);
        let mk = rng.gen_range_usize(0, 3) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut total);
    }
}
