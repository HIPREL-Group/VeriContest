use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_non_decreasing(s: Seq<i32>) -> bool {
        forall|i: int| 0 <= i < s.len() as int - 1 ==> #[trigger] s[i] <= s[i + 1]
    }

    pub open spec fn can_fix_with_one_change(nums: Seq<i32>) -> bool {
        Self::is_non_decreasing(nums)
        || exists|k: int, v: i32|
            0 <= k < nums.len() as int
            && Self::is_non_decreasing(#[trigger] nums.update(k, v))
    }

    pub open spec fn can_fix_at_index(nums: Seq<i32>, k: int) -> bool {
        &&& 0 <= k < nums.len() as int
        &&& forall|j: int|
                0 <= j < nums.len() as int - 1 ==>
                (j == k - 1 || j == k || #[trigger] nums[j] <= nums[j + 1])
        &&& (0 < k && k < nums.len() as int - 1 ==> nums[k - 1] <= nums[k + 1])
    }

    fn check_index(nums: &Vec<i32>, k: usize) -> (ok: bool)
        requires
            1 <= nums.len(),
            k < nums.len(),
        ensures
            ok <==> Self::can_fix_at_index(nums@, k as int),
    {
        let n = nums.len();
        let mut j = 0usize;

        while j + 1 < n
        {
            if nums[j] > nums[j + 1] && !(j + 1 == k || j == k) {
                return false;
            }
            j += 1;
        }

        if 0 < k && k + 1 < n && nums[k - 1] > nums[k + 1] {
            return false;
        }
        true
    }

    pub fn check_possibility(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 10_000,
            forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            result <==> Self::can_fix_with_one_change(nums@),
    {
        let n = nums.len();
        let mut k = 0usize;

        while k < n
        {
            let ok = Self::check_index(&nums, k);
            if ok {
                return true;
            }
            k += 1;
        }

        false
    }
}

} 
