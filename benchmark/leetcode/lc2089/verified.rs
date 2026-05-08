use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_less_prefix(nums: Seq<i32>, target: i32, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        count_less_prefix(nums, target, (k - 1) as nat)
            + if nums[(k - 1) as int] < target { 1int } else { 0int }
    }
}

pub open spec fn count_eq_prefix(nums: Seq<i32>, target: i32, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        count_eq_prefix(nums, target, (k - 1) as nat)
            + if nums[(k - 1) as int] == target { 1int } else { 0int }
    }
}

impl Solution {
    pub fn target_indices(nums: Vec<i32>, target: i32) -> (result: Vec<i32>)
        requires
            nums.len() <= 2147483647usize,
        ensures
            result.len() as int == count_eq_prefix(nums@, target, nums.len() as nat),
            forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i]
                == (count_less_prefix(nums@, target, nums.len() as nat) + i) as i32,
    {
        let n = nums.len();
        let mut less: usize = 0;
        let mut eq: usize = 0;
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                less as int == count_less_prefix(nums@, target, i as nat),
                eq as int == count_eq_prefix(nums@, target, i as nat),
                less <= i,
                eq <= i,
                less + eq <= i,
                found ==> eq > 0,
                !found ==> eq == 0,
                found ==> exists |j: int| 0 <= j < i && nums[j] == target,
                !found ==> forall |j: int| 0 <= j < i ==> nums[j] != target,
            decreases n - i,
        {
            proof {
                assert(i + 1 <= n);
                assert(count_less_prefix(nums@, target, (i + 1) as nat)
                    == count_less_prefix(nums@, target, i as nat)
                        + if nums[i as int] < target { 1int } else { 0int });
                assert(count_eq_prefix(nums@, target, (i + 1) as nat)
                    == count_eq_prefix(nums@, target, i as nat)
                        + if nums[i as int] == target { 1int } else { 0int });
            }
            if nums[i] < target {
                less = less + 1;
            }
            if nums[i] == target {
                eq = eq + 1;
                found = true;
            }
            i = i + 1;
        }

        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < eq
            invariant
                0 <= k <= eq,
                out.len() == k,
                n == nums.len(),
                less as int == count_less_prefix(nums@, target, n as nat),
                eq as int == count_eq_prefix(nums@, target, n as nat),
                less + eq <= n,
                found ==> exists |j: int| 0 <= j < n && nums[j] == target,
                forall |idx: int| 0 <= idx < out.len() ==> #[trigger] out[idx] == (less as int + idx) as i32,
            decreases eq - k,
        {
            proof {
                assert(k < eq);
                assert(less + k < less + eq);
                assert(less + eq <= n);
                assert(less + k < n);
            }
            let ghost old_out = out@;
            out.push((less + k) as i32);
            proof {
                assert(out@.len() == old_out.len() + 1);
                assert(old_out.len() == k as int);
                assert(out@[old_out.len() as int] == (less + k) as i32);
                assert forall |idx: int| 0 <= idx < out.len()
                    implies #[trigger] out[idx] == (less as int + idx) as i32 by {
                    if idx < old_out.len() {
                        assert(old_out[idx] == (less as int + idx) as i32);
                        assert(out[idx] == old_out[idx]);
                    } else {
                        assert(idx == old_out.len() as int);
                        assert(out[idx] == (less + k) as i32);
                    }
                }
            }
            k = k + 1;
        }
        proof {
            assert(eq as int == count_eq_prefix(nums@, target, n as nat));
            assert(out.len() as int == count_eq_prefix(nums@, target, n as nat));
            assert(forall |idx: int| 0 <= idx < out.len() ==> #[trigger] out[idx] == (less as int + idx) as i32);
        }
        out
    }
}

}
