use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_removal(nums: Seq<i32>, r: int) -> bool {
        0 <= r < nums.len() &&
        (forall |j: int| 1 <= j < nums.len() && j != r && j - 1 != r ==>
            nums[j - 1] < #[trigger] nums[j]) &&
        (0 < r && r + 1 < nums.len() ==> nums[r - 1] < nums[r + 1])
    }

    pub fn can_be_increasing(nums: Vec<i32>) -> (result: bool)
        requires
            2 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result == (exists |r: int| Self::valid_removal(nums@, r)),
    {
        let n = nums.len();
        let mut r: usize = 0;
        while r < n
            invariant
                n == nums.len(),
                2 <= n <= 1000,
                0 <= r <= n,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
                forall |t: int| 0 <= t < r as int ==> !Self::valid_removal(nums@, t),
            decreases n - r,
        {
            let mut ok = true;
            let ghost mut fail_j: int = 0;
            let ghost mut inner_failed = false;
            let mut j: usize = 1;
            while j < n
                invariant
                    n == nums.len(),
                    2 <= n <= 1000,
                    0 <= r < n,
                    1 <= j <= n,
                    ok ==> forall |t: int|
                        1 <= t < j as int && t != r as int && t - 1 != r as int ==>
                            nums[t - 1] < #[trigger] nums[t],
                    !ok ==> (inner_failed && 1 <= fail_j < j as int &&
                        fail_j != r as int && fail_j - 1 != r as int &&
                        nums[fail_j - 1] >= nums[fail_j]),
                decreases n - j,
            {
                if j != r && j - 1 != r {
                    if nums[j - 1] >= nums[j] {
                        proof {
                            inner_failed = true;
                            fail_j = j as int;
                        }
                        ok = false;
                    }
                }
                j = j + 1;
            }

            proof {
                if !ok {
                    assert(inner_failed);
                    assert(1 <= fail_j < nums.len() as int);
                    assert(fail_j != r as int && fail_j - 1 != r as int);
                    assert(nums[fail_j - 1] >= nums[fail_j]);
                }
            }

            let ghost ok_after_inner = ok;

            if ok && r > 0 && r + 1 < n && nums[r - 1] >= nums[r + 1] {
                ok = false;
            }
            if ok {
                proof {
                    assert(ok_after_inner);
                    assert forall |t: int| 1 <= t < nums.len() && t != r as int && t - 1 != r as int
                        implies nums[t - 1] < #[trigger] nums[t] by {};
                    assert(Self::valid_removal(nums@, r as int));
                }
                return true;
            } else {
                proof {
                    if !ok_after_inner {
                        assert(inner_failed);
                        assert(1 <= fail_j < nums.len() as int);
                        assert(fail_j != r as int && fail_j - 1 != r as int);
                        assert(!(nums[fail_j - 1] < nums[fail_j]));
                    } else {
                        assert(0 < r as int);
                        assert(r as int + 1 < nums.len());
                        assert(nums[r as int - 1] >= nums[r as int + 1]);
                    }
                    assert(!Self::valid_removal(nums@, r as int));
                }
            }
            r = r + 1;
        }
        false
    }
}

}
