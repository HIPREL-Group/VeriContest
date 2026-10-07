use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn product_of_range(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start
    {
        if start >= end {
            1
        } else {
            nums[start] as int * Self::product_of_range(nums, start + 1, end)
        }
    }

    /// For elements in [-1, 1], the product of any subrange is in [-1, 1].
    proof fn product_of_unit_bounded(nums: Seq<i32>, i: int, j: int)
        requires
            0 <= i <= j <= nums.len(),
            forall |k: int| i <= k < j ==> -1 <= #[trigger] nums[k] <= 1,
        ensures
            -1 <= Self::product_of_range(nums, i, j) <= 1,
        decreases j - i,
    {
        if i < j {
            Self::product_of_unit_bounded(nums, i + 1, j);
            let a = nums[i] as int;
            let p = Self::product_of_range(nums, i + 1, j);
            if a == 0 {
                assert(a * p == 0);
            } else if a == 1 {
                assert(a * p == p);
            } else {
                assert(a == -1);
                assert(a * p == -p);
            }
        }
    }

    pub fn generate_test_case(
        values: Vec<i32>,
        mutation_kind: u8,
    ) -> (result: Vec<i32>)
        requires
            1 <= values.len() <= 20_000,
            forall |i: int| 0 <= i < values.len() ==> -1 <= #[trigger] values[i] <= 1,
        ensures
            1 <= result.len() <= 20_000,
            forall |i: int| 0 <= i < result.len() ==> -10 <= #[trigger] result[i] <= 10,
            forall |i: int, j: int| 0 <= i < j <= result.len()
                ==> i32::MIN <= #[trigger] Self::product_of_range(result@, i, j) <= i32::MAX,
    {
        let nums = if mutation_kind == 0 {
            // identity
            values
        } else if mutation_kind == 1 {
            // negate first element
            let mut v = values;
            let val = v[0];
            v.set(0, -val);
            v
        } else if mutation_kind == 2 {
            // set first element to 0
            let mut v = values;
            v.set(0, 0);
            v
        } else if mutation_kind == 3 {
            // set last element to 0
            let mut v = values;
            let last = v.len() - 1;
            v.set(last, 0);
            v
        } else if mutation_kind == 4 && values.len() > 1 {
            // shrink by one
            let mut v = values;
            v.pop();
            v
        } else if mutation_kind == 5 && values.len() < 20_000 {
            // grow by one (push 0)
            let mut v = values;
            v.push(0);
            v
        } else if mutation_kind == 6 {
            // set all to 1
            let mut v = values;
            let mut idx: usize = 0;
            while idx < v.len()
                invariant
                    0 <= idx <= v.len(),
                    v.len() == values.len(),
                    1 <= v.len() <= 20_000,
                    forall |k: int| 0 <= k < idx as int ==> v[k] == 1i32,
                    forall |k: int| idx as int <= k < v.len() as int ==> v[k] == values[k],
                decreases v.len() - idx,
            {
                v.set(idx, 1);
                idx += 1;
            }
            v
        } else if mutation_kind == 7 && values.len() > 1 {
            // swap first and last
            let mut v = values;
            let last_idx = v.len() - 1;
            let first_val = v[0];
            let last_val = v[last_idx];
            v.set(0, last_val);
            v.set(last_idx, first_val);
            v
        } else if mutation_kind == 8 {
            // set all to -1
            let mut v = values;
            let mut idx: usize = 0;
            while idx < v.len()
                invariant
                    0 <= idx <= v.len(),
                    v.len() == values.len(),
                    1 <= v.len() <= 20_000,
                    forall |k: int| 0 <= k < idx as int ==> v[k] == -1i32,
                    forall |k: int| idx as int <= k < v.len() as int ==> v[k] == values[k],
                decreases v.len() - idx,
            {
                v.set(idx, -1);
                idx += 1;
            }
            v
        } else if mutation_kind == 9 {
            // set all to 0
            let mut v = values;
            let mut idx: usize = 0;
            while idx < v.len()
                invariant
                    0 <= idx <= v.len(),
                    v.len() == values.len(),
                    1 <= v.len() <= 20_000,
                    forall |k: int| 0 <= k < idx as int ==> v[k] == 0i32,
                    forall |k: int| idx as int <= k < v.len() as int ==> v[k] == values[k],
                decreases v.len() - idx,
            {
                v.set(idx, 0);
                idx += 1;
            }
            v
        } else {
            // fallback: identity
            values
        };

        proof {
            assert forall |i: int, j: int| 0 <= i < j <= nums.len()
                implies i32::MIN <= #[trigger] Self::product_of_range(nums@, i, j) <= i32::MAX
            by {
                Self::product_of_unit_bounded(nums@, i, j);
            }
        }

        nums
    }
}

} // verus!

include!("../code.rs");

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

fn gen(values: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    Solution::generate_test_case(values, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_unit_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-1, 1) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(152);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, n: &mut usize| {
        if *n >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::max_product(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *n += 1;
    };

    // Examples from description.md
    emit(vec![2, 3, -2, 4], &mut seen, &mut out, &mut n);
    emit(vec![-2, 0, -1], &mut seen, &mut out, &mut n);

    // Extra short arrays with values in [-10, 10] (known to satisfy product constraint)
    let extras: Vec<Vec<i32>> = vec![
        vec![0, 2],
        vec![-4, -3, -2],
        vec![3, -1, 4],
        vec![2, -5, -2, -4, 3],
        vec![-1, -2, -3, -4],
        vec![7],
        vec![-10, 10],
        vec![0],
        vec![0, 0, 0, 0],
        vec![10, 10, 10, 10, 10, 10, 10, 10, 10],
        vec![-10, -10, -10, -10, -10, -10, -10, -10, -10],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9],
        vec![-1, 2, -3, 4, -5, 6, -7, 8, -9],
        vec![0, 10, 0, 10, 0],
        vec![-10, 0, 10, 0, -10],
        vec![-2, 3, -4],
        vec![5, -5, 5, -5],
        vec![10],
        vec![-10],
    ];
    for e in extras {
        emit(e, &mut seen, &mut out, &mut n);
    }

    // Seed patterns for verified mutation
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![-1],
        vec![0],
        vec![1, 1],
        vec![-1, -1],
        vec![1, -1],
        vec![0, 0],
        vec![1, 0, -1],
        vec![-1, 1, -1, 1],
        vec![0, 1, 0, -1, 0],
        vec![1, 1, 1, 1, 1],
        vec![-1, -1, -1, -1],
        vec![1, -1, 1, -1, 1, -1],
    ];

    let mutation_kinds: Vec<u8> = (0..=9).collect();

    for sv in &seeds {
        for &mk in &mutation_kinds {
            let result = gen(sv.clone(), mk);
            emit(result, &mut seen, &mut out, &mut n);
        }
    }

    // Random {-1, 0, 1} arrays with diverse sizes and mutations
    while n < count {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 20_000), // max
        };
        let vals = random_unit_vec(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = gen(vals, mk);
        emit(result, &mut seen, &mut out, &mut n);
    }
}
