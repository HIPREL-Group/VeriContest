use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_sorted_range(s: Seq<i32>, lo: int, hi: int) -> bool {
        forall |i: int, j: int| lo <= i < j < hi ==> s[i] <= s[j]
    }

    pub open spec fn can_sort_by_right_shifts(s: Seq<i32>, k: int) -> bool {
        let n = s.len() as int;
        let p = n - k;
        0 <= k <= n - 1
        && Self::is_sorted_range(s, p, n)
        && Self::is_sorted_range(s, 0, p)
        && (k > 0 ==> s[n - 1] <= s[0])
    }

    pub fn minimum_right_shifts(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures
            -1 <= result,
            result < nums.len() as i32,
            result >= 0 ==> Self::can_sort_by_right_shifts(nums@, result as int),
            result == -1 ==> forall |k: int| 0 <= k < nums.len() ==> !Self::can_sort_by_right_shifts(nums@, k),
    {
        let n = nums.len();
        let mut break_count: usize = 0;
        let mut break_pos: usize = 0;
        let mut i: usize = 0;

        while i + 1 < n {
            if nums[i] > nums[i + 1] {
                if break_count == 0 {
                    break_pos = i;
                }
                break_count = break_count + 1;
            }
            i = i + 1;
        }

        if break_count == 0 {
            return 0;
        }

        if break_count >= 2 {
            return -1;
        }

        
        if nums[n - 1] <= nums[0] {
            return (n - break_pos - 1) as i32;
        }

        -1
    }
}

}
