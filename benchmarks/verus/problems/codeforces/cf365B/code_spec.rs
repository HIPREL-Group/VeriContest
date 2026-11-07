use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn good_segment(nums: Seq<i64>, l: int, r: int) -> bool {
        &&& 0 <= l < r <= nums.len()
        &&& forall|t: int| l + 2 <= t < r ==> #[trigger] nums[t] == nums[t - 1] + nums[t - 2]
    }

    pub fn longest_fibonacci_segment(nums: Vec<i64>) -> (result: usize)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            1 <= result <= nums.len(),
            exists|l: int, r: int|
                #[trigger] Self::good_segment(nums@, l, r) && result as int == r - l,
            forall|l: int, r: int|
                #[trigger] Self::good_segment(nums@, l, r) ==> r - l <= result as int,
    {
        let n = nums.len();
        if n <= 2 {
            return n;
        }

        let mut best = 2usize;
        let mut cur = 2usize;
        let mut i = 2usize;
        while i < n {
            if nums[i] == nums[i - 1] + nums[i - 2] {
                cur = cur + 1;
            } else {
                cur = 2;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}

}
