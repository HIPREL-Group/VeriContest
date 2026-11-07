use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::spec_sum(s, end - 1) + s[end - 1] as int
        }
    }

    proof fn spec_sum_bound(s: Seq<i32>, end: int)
        requires
            0 <= end <= s.len(),
            s.len() <= 1000,
            forall |i: int| 0 <= i < s.len() ==> -1_000_000 <= #[trigger] s[i] <= 1_000_000,
        ensures
            -end * 1_000_000 <= Self::spec_sum(s, end) <= end * 1_000_000,
        decreases end,
    {
        if end > 0 {
            Self::spec_sum_bound(s, end - 1);
        }
    }

    pub fn running_sum(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() as int ==> result[i] == Self::spec_sum(nums@, i + 1),
    {
        let ghost orig = nums@;
        let mut result = nums;
        let n = result.len();
        proof {
            assert(result@ =~= orig);
            assert(Self::spec_sum(orig, 0int) == 0);
        }
        let mut i: usize = 1;
        while i < n
            invariant
                n == result.len(),
                n == orig.len(),
                1 <= n <= 1000,
                1 <= i <= n,
                forall |k: int| 0 <= k < orig.len() ==> -1_000_000 <= #[trigger] orig[k] <= 1_000_000,
                forall |j: int| 0 <= j < i as int ==> result[j] == Self::spec_sum(orig, j + 1),
                forall |j: int| #![auto] i as int <= j < n as int ==> result[j] == orig[j],
            decreases n - i,
        {
            proof {
                Self::spec_sum_bound(orig, i as int);
                assert(i as int * 1_000_000 <= 1_000_000_000) by(nonlinear_arith)
                    requires i as int <= 1000;
                assert(-1_000_000_000 <= Self::spec_sum(orig, i as int) <= 1_000_000_000);
                assert(result[i as int] == orig[i as int]);
                assert(-1_000_000 <= orig[i as int] <= 1_000_000);
                assert(-1_000_000 <= result[i as int] <= 1_000_000);
                assert(-1_000_000_000 <= result[(i - 1) as int] <= 1_000_000_000);
            }
            result.set(i, result[i] + result[i - 1]);
            i = i + 1;
        }
        result
    }
}

}
