use vstd::prelude::*;

verus! {

// ---------- spec fn helpers (from spec.rs) ----------

pub open spec fn sorted_range(nums: &Vec<i32>, start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i <= j < end ==> nums[i] <= nums[j]
}

pub open spec fn pivot_ok(nums: &Vec<i32>, p: int) -> bool {
    0 <= p < nums.len() && if p == 0 {
        sorted_range(nums, 0, nums.len() as int)
    } else {
        nums[p - 1] > nums[p] && sorted_range(nums, 0, p)
            && sorted_range(nums, p, nums.len() as int)
            && forall|i: int, j: int|
                p <= i < nums.len() && 0 <= j < p ==> nums[i] <= nums[j]
    }
}

pub open spec fn rotated_sorted(nums: &Vec<i32>) -> bool {
    exists|p: int| #[trigger] pivot_ok(nums, p)
}

// ---------- generator ----------

pub fn generate_test_case(
    sorted_vals: &Vec<i32>,
    pivot: usize,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= sorted_vals.len() <= 5_000,
        forall|i: int| 0 <= i < sorted_vals.len() ==> -10_000 <= #[trigger] sorted_vals[i] <= 10_000,
        forall|i: int, j: int| 0 <= i <= j < sorted_vals.len() ==> sorted_vals[i] <= sorted_vals[j],
        0 <= pivot < sorted_vals.len(),
        pivot == 0 || sorted_vals[sorted_vals.len() - 1 as int] > sorted_vals[0],
        -10_000 <= target <= 10_000,
    ensures
        1 <= result.0.len() <= 5_000,
        forall|i: int| 0 <= i < result.0.len() ==> -10_000 <= #[trigger] result.0[i] <= 10_000,
        rotated_sorted(&result.0),
        -10_000 <= result.1 <= 10_000,
{
    let n = sorted_vals.len();
    let mut nums: Vec<i32> = Vec::new();

    // Build rotated array: sorted_vals[pivot..n] ++ sorted_vals[0..pivot]
    let mut k: usize = pivot;
    while k < n
        invariant
            0 <= pivot <= k <= n,
            n == sorted_vals.len(),
            nums.len() == (k - pivot) as int,
            1 <= n <= 5_000,
            forall|i: int| 0 <= i < sorted_vals.len() ==> -10_000 <= #[trigger] sorted_vals[i] <= 10_000,
            forall|i: int, j: int| 0 <= i <= j < sorted_vals.len() ==> sorted_vals[i] <= sorted_vals[j],
            forall|idx: int| 0 <= idx < nums.len() ==> #[trigger] nums[idx] == sorted_vals[pivot as int + idx],
        decreases n - k,
    {
        nums.push(sorted_vals[k]);
        k = k + 1;
    }

    let split = nums.len();

    let mut m: usize = 0;
    while m < pivot
        invariant
            0 <= m <= pivot,
            pivot < n,
            n == sorted_vals.len(),
            split == (n - pivot) as int,
            nums.len() == split + m as int,
            1 <= n <= 5_000,
            forall|i: int| 0 <= i < sorted_vals.len() ==> -10_000 <= #[trigger] sorted_vals[i] <= 10_000,
            forall|i: int, j: int| 0 <= i <= j < sorted_vals.len() ==> sorted_vals[i] <= sorted_vals[j],
            forall|idx: int| 0 <= idx < split ==> #[trigger] nums[idx] == sorted_vals[pivot as int + idx],
            forall|idx: int| split <= idx < split + m as int ==> #[trigger] nums[idx] == sorted_vals[idx - split],
        decreases pivot - m,
    {
        nums.push(sorted_vals[m]);
        m = m + 1;
    }

    assert(nums.len() == n);

    proof {
        // Suffix part [0, split) is sorted (from sorted_vals[pivot..n])
        assert forall|i: int, j: int| 0 <= i <= j < (n - pivot) as int implies nums[i] <= nums[j] by {
            assert(nums[i] == sorted_vals[pivot as int + i]);
            assert(nums[j] == sorted_vals[pivot as int + j]);
        };

        if pivot == 0 {
            assert forall|i: int, j: int| 0 <= i <= j < n as int implies nums[i] <= nums[j] by {
                assert(nums[i] == sorted_vals[i]);
                assert(nums[j] == sorted_vals[j]);
            };
            assert(sorted_range(&nums, 0, n as int));
            assert(pivot_ok(&nums, 0));
        } else {
            let split_i = (n - pivot) as int;

            assert(sorted_range(&nums, 0, split_i));

            // Prefix part [split_i, n) is sorted (from sorted_vals[0..pivot])
            assert forall|i: int, j: int| split_i <= i <= j < n as int implies nums[i] <= nums[j] by {
                assert(nums[i] == sorted_vals[i - split_i]);
                assert(nums[j] == sorted_vals[j - split_i]);
            };
            assert(sorted_range(&nums, split_i, n as int));

            // Break: nums[split_i - 1] > nums[split_i]
            assert(nums[split_i - 1] == sorted_vals[(n - 1) as int]);
            assert(nums[split_i] == sorted_vals[0]);
            assert(nums[split_i - 1] > nums[split_i]);

            // Cross ordering: elements in [split_i, n) <= elements in [0, split_i)
            assert forall|i: int, j: int| split_i <= i < n as int && 0 <= j < split_i implies nums[i] <= nums[j] by {
                assert(nums[i] == sorted_vals[i - split_i]);
                assert(nums[j] == sorted_vals[pivot as int + j]);
            };

            assert(pivot_ok(&nums, split_i));
        }

        assert(rotated_sorted(&nums));
    }

    // Target mutation
    let mutated_target: i32 =
        if mutation_kind == 1 {
            nums[0]
        } else if mutation_kind == 2 {
            let last = nums.len() - 1;
            nums[last]
        } else if mutation_kind == 3 {
            let mid = nums.len() / 2;
            nums[mid]
        } else if mutation_kind == 4 && nums[0] > -10_000 {
            (nums[0] - 1) as i32
        } else if mutation_kind == 5 {
            let last = nums.len() - 1;
            if nums[last] < 10_000 {
                (nums[last] + 1) as i32
            } else {
                target
            }
        } else if mutation_kind == 6 {
            0i32
        } else if mutation_kind == 7 {
            -10_000i32
        } else if mutation_kind == 8 {
            10_000i32
        } else {
            target
        };

    (nums, mutated_target)
}

} // verus!

// ---------- unverified main ----------

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

extern crate serde_json;
use serde_json::json;

#[allow(dead_code)]
mod code_solution {
    pub struct Solution;
    include!("../code.rs");
}
use code_solution::Solution;

fn make_sorted(rng: &mut Rng, n: usize, allow_dups: bool) -> Vec<i32> {
    let mut vals = Vec::with_capacity(n);
    for _ in 0..n {
        vals.push(rng.gen_range_i64(-10_000, 10_000) as i32);
    }
    vals.sort();
    if !allow_dups {
        vals.dedup();
        while vals.len() < n {
            vals.push(rng.gen_range_i64(-10_000, 10_000) as i32);
        }
        vals.sort();
        vals.truncate(n);
    }
    vals
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(81);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    macro_rules! emit {
        ($sorted:expr, $pivot:expr, $target:expr, $mk:expr) => {
            if emitted < count {
                let sorted_val: Vec<i32> = $sorted;
                let pivot_val: usize = $pivot;
                let target_val: i32 = $target;
                let mk_val: u8 = $mk;
                let (nums_out, target_out) = generate_test_case(
                    &sorted_val, pivot_val, target_val, mk_val,
                );
                let result = Solution::search(nums_out.clone(), target_out);
                let line = json!({
                    "input": {"nums": nums_out, "target": target_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    emitted += 1;
                }
            }
        };
    }

    // ---- Examples from description.md ----
    emit!(vec![0, 0, 1, 2, 2, 5, 6], 3, 0, 0);   // [2,5,6,0,0,1,2], target=0
    emit!(vec![0, 0, 1, 2, 2, 5, 6], 3, 3, 0);   // [2,5,6,0,0,1,2], target=3

    // ---- Single-element arrays with all mutations ----
    for mk in 0u8..=8 {
        emit!(vec![0], 0, 5, mk);
        emit!(vec![-10_000], 0, -10_000, mk);
        emit!(vec![10_000], 0, 10_000, mk);
    }

    // ---- Small hand-crafted cases ----
    emit!(vec![1, 2, 3, 4, 5], 0, 3, 0);
    emit!(vec![1, 2, 3, 4, 5], 0, 6, 0);
    emit!(vec![1, 2, 3, 4, 5], 2, 1, 0);
    emit!(vec![1, 2, 3, 4, 5], 4, 5, 0);
    emit!(vec![1, 1, 2, 3, 3], 2, 3, 0);
    emit!(vec![1, 1, 1, 1, 1], 0, 1, 0);
    emit!(vec![1, 1, 1, 1, 1], 0, 2, 0);
    emit!(vec![-10_000, -10_000, 10_000, 10_000], 2, 0, 0);
    emit!(vec![-10_000, 0, 10_000], 1, 10_000, 0);

    // ---- Random diverse test cases ----
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };

        let allow_dups = rng.gen_range_usize(0, 1) == 0;
        let sorted = make_sorted(&mut rng, n, allow_dups);

        let pivot = if n == 1 {
            0
        } else if sorted[sorted.len() - 1] <= sorted[0] {
            0
        } else {
            if rng.gen_range_usize(0, 3) == 0 { 0 } else { rng.gen_range_usize(1, n - 1) }
        };

        let target = match rng.gen_range_usize(0, 4) {
            0 => -10_000i32,
            1 => 10_000i32,
            2 => 0i32,
            3 => rng.gen_range_i64(-10_000, 10_000) as i32,
            _ => rng.gen_range_i64(-10_000, 10_000) as i32,
        };

        let mk = rng.gen_range_usize(0, 8) as u8;
        emit!(sorted, pivot, target, mk);
    }

    eprintln!("Generated {} test cases", emitted);
}
