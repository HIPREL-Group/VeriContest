use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn occurrence_count(nums: Seq<i32>, val: int, j: int) -> int
    decreases j,
{
    if j <= 0 {
        0
    } else {
        occurrence_count(nums, val, j - 1)
            + if nums[j - 1] as int == val { 1int } else { 0int }
    }
}

pub open spec fn is_unique(nums: Seq<i32>, i: int) -> bool {
    occurrence_count(nums, nums[i] as int, nums.len() as int) == 1
}

pub open spec fn unique_sum(nums: Seq<i32>, i: int) -> int
    decreases nums.len() - i,
{
    if i >= nums.len() {
        0
    } else {
        (if is_unique(nums, i) { nums[i] as int } else { 0int })
            + unique_sum(nums, i + 1)
    }
}

proof fn lemma_occurrence_count_bound(nums: Seq<i32>, val: int, j: int)
    requires
        0 <= j <= nums.len(),
    ensures
        0 <= occurrence_count(nums, val, j) <= j,
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_occurrence_count_bound(nums, val, j - 1);
    }
}

proof fn lemma_unique_sum_bound(nums: Seq<i32>, i: int)
    requires
        0 <= i,
        nums.len() <= 100,
        forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
    ensures
        0 <= unique_sum(nums, i),
        unique_sum(nums, i) <= if i < nums.len() { (nums.len() - i) * 100 } else { 0int },
    decreases nums.len() - i,
{
    if i >= nums.len() {
    } else {
        lemma_unique_sum_bound(nums, i + 1);
        assert(unique_sum(nums, i) ==
            (if is_unique(nums, i) { nums[i] as int } else { 0int })
            + unique_sum(nums, i + 1));
        if is_unique(nums, i) {
            assert(1 <= nums[i] <= 100);
        }
        assert((nums.len() - (i + 1)) * 100 + 100 <= (nums.len() - i) * 100) by(nonlinear_arith)
            requires 0 <= i < nums.len() <= 100;
    }
}

impl Solution {
    pub fn sum_of_unique(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            res as int == unique_sum(nums@, 0),
    {
        let n = nums.len();
        let mut sum: i64 = 0;
        let mut i: usize = 0;

        proof {
            lemma_unique_sum_bound(nums@, 0);
            assert(unique_sum(nums@, 0) <= nums.len() * 100);
            assert(nums.len() * 100 <= 10000) by(nonlinear_arith)
                requires nums.len() <= 100;
        }

        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                0 <= i <= n,
                0 <= sum <= 10000,
                sum == unique_sum(nums@, 0) - unique_sum(nums@, i as int),
            decreases n - i,
        {
            let mut count: i64 = 0;
            let mut j: usize = 0;

            while j < n
                invariant
                    n == nums.len(),
                    1 <= nums.len() <= 100,
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                    0 <= i < n,
                    0 <= j <= n,
                    0 <= count <= j as int,
                    count == occurrence_count(nums@, nums[i as int] as int, j as int),
                decreases n - j,
            {
                proof {
                    lemma_occurrence_count_bound(nums@, nums[i as int] as int, (j + 1) as int);
                }
                if nums[j] == nums[i] {
                    count = count + 1;
                }
                j += 1;
            }

            assert(count == occurrence_count(nums@, nums[i as int] as int, n as int));

            proof {
                
                assert(unique_sum(nums@, i as int) ==
                    (if is_unique(nums@, i as int) { nums[i as int] as int } else { 0int })
                    + unique_sum(nums@, (i + 1) as int));

                lemma_unique_sum_bound(nums@, (i + 1) as int);
                lemma_unique_sum_bound(nums@, 0);
            }

            if count == 1 {
                proof {
                    assert(is_unique(nums@, i as int));
                }
                sum = sum + nums[i] as i64;
            } else {
                proof {
                    assert(!is_unique(nums@, i as int));
                }
            }

            assert(sum == unique_sum(nums@, 0) - unique_sum(nums@, (i + 1) as int));

            proof {
                lemma_unique_sum_bound(nums@, (i + 1) as int);
                assert(unique_sum(nums@, (i + 1) as int) >= 0);
                assert(unique_sum(nums@, 0) <= 10000);
            }

            i += 1;
        }

        assert(unique_sum(nums@, n as int) == 0int);
        assert(sum == unique_sum(nums@, 0));

        sum as i32
    }
}

} 
