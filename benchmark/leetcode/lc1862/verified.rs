use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

fn main() {}

verus! {

pub struct Solution;

pub open spec fn inner_sum(nums: Seq<i32>, i: int, end_j: int) -> int
    decreases end_j,
{
    if end_j <= 0 {
        0
    } else {
        inner_sum(nums, i, end_j - 1) + (nums[i] as int) / (nums[end_j - 1] as int)
    }
}

pub open spec fn outer_sum(nums: Seq<i32>, end_i: int) -> int
    decreases end_i,
{
    if end_i <= 0 {
        0
    } else {
        outer_sum(nums, end_i - 1) + inner_sum(nums, end_i - 1, nums.len() as int)
    }
}

proof fn lemma_inner_sum_nonneg(nums: Seq<i32>, i: int, end_j: int)
    requires
        0 <= i < nums.len(),
        0 <= end_j <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 1,
    ensures
        inner_sum(nums, i, end_j) >= 0,
    decreases end_j,
{
    if end_j > 0 {
        lemma_inner_sum_nonneg(nums, i, end_j - 1);
    }
}

proof fn lemma_outer_sum_nonneg(nums: Seq<i32>, end_i: int)
    requires
        0 <= end_i <= nums.len(),
        nums.len() >= 1,
        forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 1,
    ensures
        outer_sum(nums, end_i) >= 0,
    decreases end_i,
{
    if end_i > 0 {
        lemma_outer_sum_nonneg(nums, end_i - 1);
        lemma_inner_sum_nonneg(nums, end_i - 1, nums.len() as int);
    }
}

proof fn lemma_mod_add(a: int, b: int, m: int)
    requires
        a >= 0,
        b >= 0,
        m > 0,
    ensures
        (a % m + b) % m == (a + b) % m,
{
    lemma_fundamental_div_mod(a, m);
    let q = a / m;
    assert(a % m + b == (a + b) + (-q) * m) by(nonlinear_arith)
        requires(a == m * q + a % m);
    lemma_mod_multiples_vanish(-q, a + b, m);
}








impl Solution {
    pub fn sum_of_floored_pairs(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            result as int == outer_sum(nums@, nums.len() as int) % 1_000_000_007,
    {
        let n = nums.len();
        let modulo: i64 = 1_000_000_007;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                modulo == 1_000_000_007,
                1 <= nums.len() <= 100_000,
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
                sum as int == outer_sum(nums@, i as int) % 1_000_000_007,
                0 <= sum < 1_000_000_007,
                outer_sum(nums@, i as int) >= 0,
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= i < n,
                    0 <= j <= n,
                    n == nums.len(),
                    modulo == 1_000_000_007,
                    1 <= nums.len() <= 100_000,
                    forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
                    sum as int == (outer_sum(nums@, i as int) + inner_sum(nums@, i as int, j as int)) % 1_000_000_007,
                    0 <= sum < 1_000_000_007,
                    outer_sum(nums@, i as int) >= 0,
                    inner_sum(nums@, i as int, j as int) >= 0,
                decreases n - j,
            {
                let div_val = (nums[i] as i64) / (nums[j] as i64);
                proof {
                    let total = outer_sum(nums@, i as int) + inner_sum(nums@, i as int, j as int);
                    assert(1 <= nums@[i as int] <= 100_000);
                    assert(1 <= nums@[j as int] <= 100_000);
                    assert(0 <= div_val <= 100_000);
                    lemma_mod_add(total, div_val as int, 1_000_000_007);
                    lemma_inner_sum_nonneg(nums@, i as int, (j + 1) as int);
                }
                sum = (sum + div_val) % modulo;
                j = j + 1;
            }
            proof {
                lemma_outer_sum_nonneg(nums@, (i + 1) as int);
            }
            i = i + 1;
        }
        (sum % modulo) as i32
    }
}

}
