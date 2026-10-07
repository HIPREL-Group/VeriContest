use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: &mut Vec<i32>, mutation_kind: u8)
    requires
        1 <= old(nums).len() <= 30_000,
        forall|i: int| 0 <= i < old(nums).len() ==>
            -10_000 <= #[trigger] old(nums)[i] <= 10_000,
        forall|i: int, j: int| 0 <= i <= j < old(nums).len() ==>
            old(nums)[i] <= old(nums)[j],
    ensures
        1 <= old(nums).len() <= 30_000,
        forall|i: int| 0 <= i < old(nums).len() ==>
            -10_000 <= #[trigger] old(nums)[i] <= 10_000,
        forall|i: int, j: int| 0 <= i <= j < old(nums).len() ==>
            old(nums)[i] <= old(nums)[j],
{
    if mutation_kind == 0 {
        // identity — no change
    } else if mutation_kind == 1 && nums.len() > 1 {
        // set last element = second-to-last (create duplicate at end)
        let last = nums.len() - 1;
        let val = nums[last - 1];
        let ghost pre = nums@;
        nums.set(last, val);
        proof {
            assert forall|i: int, j: int| 0 <= i <= j < nums.len() as int
                implies nums[i] <= nums[j] by {
                if j < last as int {
                    assert(nums[i] == pre[i]);
                    assert(nums[j] == pre[j]);
                } else if i < last as int {
                    assert(nums[i] == pre[i]);
                    assert(nums[j as int] == val);
                    assert(pre[i] <= pre[last as int - 1]);
                }
            };
        }
    } else if mutation_kind == 2 && nums.len() < 30_000 {
        // grow: duplicate last element
        let last_val = nums[nums.len() - 1];
        assert(forall|i: int| 0 <= i < nums.len() ==> nums[i] <= last_val);
        nums.push(last_val);
    } else if mutation_kind == 3 && nums.len() > 1 {
        // shrink: remove last element
        let ghost pre = nums@;
        let _ = nums.pop();
        proof {
            assert(nums@ =~= pre.subrange(0, pre.len() - 1));
            assert forall|i: int| 0 <= i < nums.len() implies
                -10_000 <= #[trigger] nums[i] <= 10_000 by {
                assert(nums[i] == pre[i]);
            };
            assert forall|i: int, j: int| 0 <= i <= j < nums.len() as int
                implies nums[i] <= nums[j] by {
                assert(nums[i] == pre[i]);
                assert(nums[j] == pre[j]);
            };
        }
    } else if mutation_kind == 4 && nums.len() >= 2 {
        // set first element = second element (create duplicate at start)
        let val = nums[1];
        let ghost pre = nums@;
        nums.set(0, val);
        proof {
            assert forall|i: int| 0 <= i < nums.len() as int implies
                -10_000 <= #[trigger] nums[i] <= 10_000 by {
                if i == 0 {
                    assert(nums[0] == val);
                    assert(val == pre[1]);
                } else {
                    assert(nums[i] == pre[i]);
                }
            };
            assert forall|i: int, j: int| 0 <= i <= j < nums.len() as int
                implies nums[i] <= nums[j] by {
                if i == 0 && j == 0 {
                    // nums[0] <= nums[0] trivially
                } else if i == 0 {
                    assert(j >= 1);
                    assert(nums[0] == val);
                    assert(val == pre[1]);
                    assert(nums[j] == pre[j]);
                    // pre is sorted: 1 <= j, so pre[1] <= pre[j]
                    assert(pre[1] <= pre[j]);
                } else {
                    assert(nums[i] == pre[i]);
                    assert(nums[j] == pre[j]);
                }
            };
        }
    } else {
        // fallback — no change
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

/// Build a sorted (non-decreasing) array of length `n` with values in
/// [-10_000, 10_000]. `strategy` controls duplicate density.
fn build_sorted_array(rng: &mut Rng, n: usize, strategy: u8) -> Vec<i32> {
    assert!(n >= 1 && n <= 30_000);
    let mut arr = Vec::with_capacity(n);
    let base = rng.gen_range_i64(-10_000, 10_000) as i32;
    arr.push(base);
    for _ in 1..n {
        let prev = *arr.last().unwrap() as i64;
        let delta: i64 = match strategy {
            0 => 0, // all same (maximum duplicates)
            1 => {
                // mostly duplicates (70% chance of 0 delta)
                if rng.gen_range_usize(0, 99) < 70 { 0 }
                else { rng.gen_range_i64(1, 3) }
            }
            2 => {
                // mixed duplicates/increases
                if rng.gen_range_usize(0, 99) < 40 { 0 }
                else { rng.gen_range_i64(1, 5) }
            }
            3 => {
                // mostly unique (10% duplicates)
                if rng.gen_range_usize(0, 99) < 10 { 0 }
                else { rng.gen_range_i64(1, 10) }
            }
            _ => rng.gen_range_i64(1, 20), // strictly increasing
        };
        let next = std::cmp::min(prev + delta, 10_000) as i32;
        arr.push(next);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(80);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let mut nums_clone = nums.clone();
        let k = Solution::remove_duplicates(&mut nums_clone);
        let prefix: Vec<i32> = nums_clone[..k as usize].to_vec();
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": {"k": k, "nums": prefix}
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 1, 1, 2, 2, 3], &mut seen, &mut out, &mut emitted);
    emit(vec![0, 0, 1, 1, 1, 1, 2, 3, 3], &mut seen, &mut out, &mut emitted);

    // Boundary and interesting cases
    let interesting: Vec<Vec<i32>> = vec![
        vec![1],
        vec![-10_000],
        vec![10_000],
        vec![0],
        vec![0, 0, 0, 0, 0],
        vec![-10_000, -10_000, 0, 0, 10_000, 10_000],
        vec![-10_000, -5_000, 0, 5_000, 10_000],
        vec![-1, 0, 1],
        vec![-10_000, 10_000],
        vec![42, 42, 42, 42, 42, 42, 42, 42, 42, 42],
        vec![-10_000, -9_999, -9_998, -9_997, -9_996],
        vec![9_996, 9_997, 9_998, 9_999, 10_000],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        vec![1, 1, 2, 2, 3, 3],
        vec![1, 1, 1, 2, 2, 2, 3, 3, 3],
        vec![1, 2, 3, 4, 5],
    ];
    for nums in interesting {
        emit(nums, &mut seen, &mut out, &mut emitted);
    }

    // Systematic: strategies × mutations
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];
    for strat in 0..5u8 {
        for &mk in &mutation_kinds {
            if emitted >= count { break; }
            let n = rng.gen_range_usize(2, 20);
            let mut nums = build_sorted_array(&mut rng, n, strat);
            generate_test_case(&mut nums, mk);
            emit(nums, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random: diverse sizes
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(5, 20),         // small
            2 => rng.gen_range_usize(20, 100),       // medium
            3 => rng.gen_range_usize(100, 1000),     // large
            _ => rng.gen_range_usize(1000, 5000),    // very large
        };
        let strat = rng.gen_range_usize(0, 4) as u8;
        let mk = rng.gen_range_usize(0, 4) as u8;
        let mut nums = build_sorted_array(&mut rng, n, strat);
        generate_test_case(&mut nums, mk);
        emit(nums, &mut seen, &mut out, &mut emitted);
    }

    eprintln!("Generated {} test cases to {:?}", emitted, out_path);
}
