use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_prefix_sum(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_prefix_sum(nums, k - 1) + nums[k - 1] as int
    }
}

proof fn lemma_prefix_sum_step(nums: Seq<i32>, j: int)
    requires
        0 <= j < nums.len(),
    ensures
        spec_prefix_sum(nums, j + 1) == spec_prefix_sum(nums, j) + nums[j] as int,
{
}

proof fn lemma_prefix_sum_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums[i] <= 100000,
    ensures
        -100000 * k <= spec_prefix_sum(nums, k) <= 100000 * k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_prefix_sum_bounds(nums, k - 1);
        assert(-100000 * (k - 1) - 100000 == -100000 * k) by (nonlinear_arith);
        assert(100000 * (k - 1) + 100000 == 100000 * k) by (nonlinear_arith);
    }
}

pub struct NumArray {
    pub prefix: Vec<i64>,
}

impl NumArray {
    pub fn new(nums: Vec<i32>) -> (result: Self)
        requires
            1 <= nums.len() <= 10000,
            forall |i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums[i] <= 100000,
        ensures
            result.prefix@.len() == nums.len() + 1,
            result.prefix@[0] == 0,
            forall |i: int| 0 <= i < nums.len() ==>
                result.prefix@[i + 1] == result.prefix@[i] + nums[i] as int,
    {
        let n = nums.len();
        let mut prefix: Vec<i64> = Vec::new();
        prefix.push(0i64);
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 10000,
                0 <= i <= n,
                prefix@.len() == i + 1,
                prefix@[0] == 0,
                forall |j: int| 0 <= j < i as int ==>
                    #[trigger] prefix@[j + 1] == spec_prefix_sum(nums@, j + 1),
                forall |j: int| 0 <= j <= i as int ==>
                    -1_000_000_000 <= (#[trigger] prefix@[j]) <= 1_000_000_000,
                forall |k: int| 0 <= k < nums.len() ==> -100000 <= #[trigger] nums[k] <= 100000,
            decreases n - i,
        {
            proof {
                lemma_prefix_sum_step(nums@, i as int);
                lemma_prefix_sum_bounds(nums@, (i + 1) as int);
                let ii = i as int;
                assert(ii < 10000);
                assert(-100000 * (ii + 1) >= -1_000_000_000) by (nonlinear_arith)
                    requires ii < 10000;
                assert(100000 * (ii + 1) <= 1_000_000_000) by (nonlinear_arith)
                    requires ii < 10000;
            }
            let next = prefix[i] + nums[i] as i64;
            prefix.push(next);
            proof {
                if i as int > 0 {
                    assert(prefix@[(i as int - 1) + 1] == spec_prefix_sum(nums@, (i as int - 1) + 1));
                } else {
                    assert(prefix@[0] == 0);
                    assert(spec_prefix_sum(nums@, 0) == 0);
                }
            }
            i += 1;
        }
        proof {
            assert(prefix@.len() == n + 1);
            assert forall |ii: int| 0 <= ii < n implies
                prefix@[ii + 1] == prefix@[ii] + nums@[ii] as int by {
                assert(prefix@[ii + 1] == spec_prefix_sum(nums@, ii + 1));
                if ii > 0 {
                    assert(prefix@[(ii - 1) + 1] == spec_prefix_sum(nums@, (ii - 1) + 1));
                }
                lemma_prefix_sum_step(nums@, ii);
            }
        }
        NumArray { prefix }
    }

    pub fn sum_range(&self, left: i32, right: i32) -> (result: i32)
        requires
            self.prefix@.len() >= 1,
            0 <= left <= right < (self.prefix@.len() - 1) as int,
            forall |i: int| 0 <= i < self.prefix@.len() ==>
                -1_000_000_000 <= (#[trigger] self.prefix@[i]) <= 1_000_000_000,
        ensures
            result as int == self.prefix@[right as int + 1] - self.prefix@[left as int],
    {
        let r = right as usize;
        let l = left as usize;
        (self.prefix[r + 1] - self.prefix[l]) as i32
    }
}

}
