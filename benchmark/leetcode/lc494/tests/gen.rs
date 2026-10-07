use vstd::prelude::*;

verus! {

// Spec fn helpers from spec.rs (standalone versions without Self::)

pub open spec fn prefix_sum(nums: Seq<i32>, end: nat) -> int
    decreases end,
{
    if end == 0 {
        0
    } else {
        prefix_sum(nums, (end - 1) as nat) + nums[(end - 1) as int] as int
    }
}

pub open spec fn seq_sum(nums: Seq<i32>) -> int {
    prefix_sum(nums, nums.len() as nat)
}

// Proof lemma: bounded elements imply bounded prefix sum
proof fn prefix_sum_upper_bound(nums: Seq<i32>, end: nat, bound: int)
    requires
        end <= nums.len(),
        bound >= 0,
        forall|i: int| 0 <= i < end ==> 0 <= #[trigger] nums[i] <= bound,
    ensures
        0 <= prefix_sum(nums, end),
        prefix_sum(nums, end) <= end as int * bound,
    decreases end,
{
    if end > 0 {
        let prev = (end - 1) as nat;
        prefix_sum_upper_bound(nums, prev, bound);
        assert(0 <= nums[(end - 1) as int] <= bound);
        assert((end - 1) as int * bound + bound == end as int * bound) by(nonlinear_arith);
    }
}

pub fn generate_test_case(
    base_vals: Vec<i32>,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= base_vals.len() <= 20,
        forall|i: int| 0 <= i < base_vals.len() ==> 0 <= #[trigger] base_vals[i] <= 50,
        -1000 <= target <= 1000,
    ensures
        1 <= result.0.len() <= 20,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        seq_sum(result.0@) <= 1000,
        -1000 <= result.1 <= 1000,
{
    if mutation_kind == 1 {
        // Set all elements to 0 (edge case: zero array)
        let mut nums = base_vals;
        let n = nums.len();
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == n,
                1 <= n <= 20,
                forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 50,
            decreases nums.len() - i,
        {
            nums.set(i, 0i32);
            i += 1;
        }
        proof {
            prefix_sum_upper_bound(nums@, nums.len() as nat, 50);
        }
        (nums, target)
    } else if mutation_kind == 2 && base_vals.len() > 1 {
        // Shrink: pop last element
        let mut nums = base_vals;
        nums.pop();
        proof {
            assert(forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 50);
            prefix_sum_upper_bound(nums@, nums.len() as nat, 50);
        }
        (nums, target)
    } else if mutation_kind == 3 {
        // Set last element to 0
        let mut nums = base_vals;
        let last = nums.len() - 1;
        nums.set(last, 0i32);
        proof {
            assert(forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 50);
            prefix_sum_upper_bound(nums@, nums.len() as nat, 50);
        }
        (nums, target)
    } else if mutation_kind == 4 {
        // Nudge first element up (cap at 50)
        let mut nums = base_vals;
        if nums[0] < 50 {
            let v = nums[0] + 1;
            nums.set(0, v);
        }
        proof {
            assert(forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 50);
            prefix_sum_upper_bound(nums@, nums.len() as nat, 50);
        }
        (nums, target)
    } else if mutation_kind == 5 {
        // Nudge first element down (min at 0)
        let mut nums = base_vals;
        if nums[0] > 0 {
            let v = nums[0] - 1;
            nums.set(0, v);
        }
        proof {
            assert(forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 50);
            prefix_sum_upper_bound(nums@, nums.len() as nat, 50);
        }
        (nums, target)
    } else if mutation_kind == 6 {
        // Negate target
        proof {
            prefix_sum_upper_bound(base_vals@, base_vals.len() as nat, 50);
        }
        (base_vals, -target)
    } else if mutation_kind == 7 {
        // Set target to 0
        proof {
            prefix_sum_upper_bound(base_vals@, base_vals.len() as nat, 50);
        }
        (base_vals, 0i32)
    } else if mutation_kind == 8 && base_vals.len() < 20 {
        // Grow: push a 0 element
        let mut nums = base_vals;
        nums.push(0i32);
        proof {
            assert(forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 50);
            prefix_sum_upper_bound(nums@, nums.len() as nat, 50);
        }
        (nums, target)
    } else {
        // Identity / fallback
        proof {
            prefix_sum_upper_bound(base_vals@, base_vals.len() as nat, 50);
        }
        (base_vals, target)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut generated = 0usize;

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 1, 1, 1, 1], 3),
        (vec![1], 1),
    ];
    for (nums, target) in &examples {
        if generated >= count { break; }
        let output = Solution::find_target_sum_ways(nums.clone(), *target);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "target": target},
            "output": output
        })).unwrap();
        generated += 1;
    }

    // Generate random test cases with diverse sizes and mutations
    while generated < count {
        // Size classes for array length
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 2),       // tiny
            1 => rng.gen_range_usize(3, 5),        // small
            2 => rng.gen_range_usize(6, 10),       // medium
            3 => rng.gen_range_usize(11, 15),      // large
            _ => rng.gen_range_usize(16, 20),      // max
        };

        // Generate base_vals with elements in 0..=50
        let mut base_vals: Vec<i32> = Vec::new();
        for _ in 0..n {
            let val: i32 = if rng.gen_range_usize(0, 4) == 0 {
                // Boundary values ~20% of the time
                let boundaries = [0i32, 1, 50, 25, 10];
                boundaries[rng.gen_range_usize(0, 4)]
            } else {
                rng.gen_range_i64(0, 50) as i32
            };
            base_vals.push(val);
        }

        // Generate target with boundary values mixed in
        let target: i32 = if rng.gen_range_usize(0, 4) == 0 {
            let boundaries = [0i32, 1, -1, 1000, -1000, 500, -500];
            boundaries[rng.gen_range_usize(0, 6)]
        } else {
            rng.gen_range_i64(-1000, 1000) as i32
        };

        // Apply mutation
        let mk = rng.gen_range_usize(0, 8) as u8;
        let (nums, tgt) = generate_test_case(base_vals, target, mk);

        let output = Solution::find_target_sum_ways(nums.clone(), tgt);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "target": tgt},
            "output": output
        })).unwrap();
        generated += 1;
    }
}
