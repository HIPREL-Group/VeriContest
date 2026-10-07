use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: &mut Vec<i32>, mutation_kind: u8)
    requires
        1 <= old(nums).len() <= 30_000,
        forall |i: int| 0 <= i < old(nums).len() ==>
            -100 <= #[trigger] old(nums)[i] <= 100,
        forall |i: int, j: int| 0 <= i <= j < old(nums).len() ==>
            old(nums)[i] <= old(nums)[j],
    ensures
        1 <= old(nums).len() <= 30_000,
        forall |i: int| 0 <= i < old(nums).len() ==>
            -100 <= #[trigger] old(nums)[i] <= 100,
        forall |i: int, j: int| 0 <= i <= j < old(nums).len() ==>
            old(nums)[i] <= old(nums)[j],
        1 <= nums.len() <= 30_000,
        forall |i: int| 0 <= i < nums.len() ==>
            -100 <= #[trigger] nums[i] <= 100,
        forall |i: int, j: int| 0 <= i <= j < nums.len() ==>
            nums[i] <= nums[j],
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
            assert forall |i: int, j: int| 0 <= i <= j < nums.len() as int
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
        assert(forall |i: int| 0 <= i < nums.len() ==> nums[i] <= last_val);
        nums.push(last_val);
    } else if mutation_kind == 3 && nums.len() > 1 {
        // shrink: remove last element
        let ghost pre = nums@;
        let _ = nums.pop();
        proof {
            assert(nums@ =~= pre.subrange(0, pre.len() - 1));
            assert forall |i: int| 0 <= i < nums.len() implies
                -100 <= #[trigger] nums[i] <= 100 by {
                assert(nums[i] == pre[i]);
            };
            assert forall |i: int, j: int| 0 <= i <= j < nums.len() as int
                implies nums[i] <= nums[j] by {
                assert(nums[i] == pre[i]);
                assert(nums[j] == pre[j]);
            };
        }
    } else if mutation_kind == 4 {
        // all same: set every element to nums[0]
        let val = nums[0];
        let n = nums.len();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                nums.len() == n,
                1 <= n <= 30_000,
                -100 <= val <= 100,
                forall |j: int| 0 <= j < k as int ==> nums[j] == val,
            decreases n - k,
        {
            nums.set(k, val);
            k += 1;
        }
        proof {
            assert forall |i: int| 0 <= i < nums.len() implies
                -100 <= #[trigger] nums[i] <= 100 by {
                assert(nums[i] == val);
            };
            assert forall |i: int, j: int| 0 <= i <= j < nums.len() as int
                implies nums[i] <= nums[j] by {
                assert(nums[i] == val);
                assert(nums[j] == val);
            };
        }
    } else {
        // fallback identity
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

fn mutate(nums: &mut Vec<i32>, mutation_kind: u8) {
    generate_test_case(nums, mutation_kind);
}

fn build_sorted_array(rng: &mut Rng, n: usize, strategy: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(n);
    let base = rng.gen_range_i64(-100, 100) as i32;
    arr.push(base);
    let mut cur = base;
    for _ in 1..n {
        let delta: i32 = match strategy {
            0 => 0,                                       // all same
            1 => 1,                                       // consecutive distinct
            2 => rng.gen_range_usize(0, 1) as i32,        // mix dups/distinct
            3 => rng.gen_range_usize(0, 5) as i32,        // small gaps
            _ => rng.gen_range_usize(0, 20) as i32,       // varied gaps
        };
        cur = std::cmp::min(cur + delta, 100);
        arr.push(cur);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
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
    emit(vec![1, 1, 2], &mut seen, &mut out, &mut emitted);
    emit(vec![0, 0, 1, 1, 1, 2, 2, 3, 3, 4], &mut seen, &mut out, &mut emitted);

    // Boundary and interesting cases
    let interesting: Vec<Vec<i32>> = vec![
        vec![1],
        vec![-100],
        vec![100],
        vec![0],
        vec![0, 0, 0, 0, 0],
        vec![-100, -100, 0, 0, 100, 100],
        vec![-100, -50, 0, 50, 100],
        vec![-1, 0, 1],
        vec![-100, 100],
        vec![42, 42, 42, 42, 42, 42, 42, 42, 42, 42],
        vec![-100, -99, -98, -97, -96],
        vec![96, 97, 98, 99, 100],
    ];
    for nums in interesting {
        emit(nums, &mut seen, &mut out, &mut emitted);
    }

    // Generate with mutations across size classes and strategies
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    // Systematic: boundary bases × strategies × mutations
    let bases: Vec<i32> = vec![-100, -50, -1, 0, 1, 50, 100];
    for &_base in &bases {
        for strat in 0..5 {
            for &mk in &mutation_kinds {
                if emitted >= count { break; }
                let n = rng.gen_range_usize(2, 15);
                let mut nums = build_sorted_array(&mut rng, n, strat);
                mutate(&mut nums, mk);
                emit(nums, &mut seen, &mut out, &mut emitted);
            }
        }
    }

    // Random: diverse sizes
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),           // tiny
            1 => rng.gen_range_usize(5, 20),           // small
            2 => rng.gen_range_usize(20, 100),         // medium
            3 => rng.gen_range_usize(100, 1000),       // large
            _ => rng.gen_range_usize(1000, 5000),      // very large
        };
        let strat = rng.gen_range_usize(0, 4);
        let mk = rng.gen_range_usize(0, 4) as u8;
        let mut nums = build_sorted_array(&mut rng, n, strat);
        mutate(&mut nums, mk);
        emit(nums, &mut seen, &mut out, &mut emitted);
    }
}
