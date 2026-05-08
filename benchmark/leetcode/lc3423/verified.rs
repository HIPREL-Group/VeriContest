use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

pub open spec fn spec_adj_diff(nums: Seq<i32>, n: int, j: int) -> int {
    if j == 0 {
        spec_abs(nums[0] as int - nums[n - 1] as int)
    } else {
        spec_abs(nums[j] as int - nums[j - 1] as int)
    }
}

pub open spec fn spec_max_diff(nums: Seq<i32>, n: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if spec_adj_diff(nums, n, k - 1) > spec_max_diff(nums, n, k - 1) {
        spec_adj_diff(nums, n, k - 1)
    } else {
        spec_max_diff(nums, n, k - 1)
    }
}

proof fn lemma_max_diff_bounds(nums: Seq<i32>, n: int, k: int)
    requires
        0 <= k <= n,
        n == nums.len(),
        2 <= n <= 100,
        forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
    ensures
        0 <= spec_max_diff(nums, n, k) <= 200,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_max_diff_bounds(nums, n, k - 1);
    }
}

impl Solution {
    pub fn max_adjacent_distance(nums: Vec<i32>) -> (diff: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            diff == spec_max_diff(nums@, nums.len() as int, nums.len() as int),
    {
        let n = nums.len();
        let mut d = nums[0] - nums[n - 1];
        if d < 0 {
            d = -d;
        }
        assert(d as int == spec_adj_diff(nums@, n as int, 0int));
        let mut diff = d;
        assert(spec_max_diff(nums@, n as int, 0int) == 0);
        assert(d >= 0);
        assert(diff as int == spec_max_diff(nums@, n as int, 1int));
        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                2 <= n <= 100,
                forall |j: int| 0 <= j < nums.len() ==> -100 <= #[trigger] nums[j] <= 100,
                1 <= i <= n,
                diff as int == spec_max_diff(nums@, n as int, i as int),
                0 <= diff <= 200,
            decreases n - i,
        {
            proof {
                lemma_max_diff_bounds(nums@, n as int, i as int);
            }
            let mut d = nums[i] - nums[i - 1];
            if d < 0 {
                d = -d;
            }
            assert(d as int == spec_adj_diff(nums@, n as int, i as int));
            if d > diff {
                diff = d;
            }
            i += 1;
        }
        diff
    }
}

} 
