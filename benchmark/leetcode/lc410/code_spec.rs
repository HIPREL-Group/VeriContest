use vstd::prelude::*;
fn main() {}
verus! {
pub struct Solution;
impl Solution {
    
    pub open spec fn sum_range_spec(nums: Seq<i32>, lo: int, hi: int) -> int
        decreases hi - lo
    {
        if hi <= lo { 0 }
        else { Self::sum_range_spec(nums, lo, hi - 1) + nums[hi - 1] as int }
    }

    
    pub open spec fn is_valid_split_spec(n: int, k: int, cuts: Seq<int>) -> bool {
        k >= 1
        && cuts.len() == k + 1
        && cuts[0] == 0
        && cuts[k as int] == n
        && forall|i: int|
            #![trigger cuts[i]]
            #![trigger cuts[i + 1]]
            0 <= i < k ==> cuts[i] < cuts[i + 1]
    }

    
    pub open spec fn max_segment_sum_spec(nums: Seq<i32>, k: int, cuts: Seq<int>) -> int
        decreases k
    {
        if k <= 1 {
            Self::sum_range_spec(nums, cuts[0], cuts[1])
        } else {
            let prev = Self::max_segment_sum_spec(nums, k - 1, cuts);
            let last = Self::sum_range_spec(nums, cuts[k - 1], cuts[k as int]);
            if last > prev { last } else { prev }
        }
    }

    
    pub open spec fn greedy_count_spec(
        nums: Seq<i32>, max_sum: int, i: int, current_sum: int,
    ) -> int
        decreases nums.len() - i
    {
        if i >= nums.len() { 1 }
        else if current_sum + nums[i] as int > max_sum {
            1 + Self::greedy_count_spec(nums, max_sum, i + 1, nums[i] as int)
        } else {
            Self::greedy_count_spec(nums, max_sum, i + 1, current_sum + nums[i] as int)
        }
    }

    
    pub open spec fn max_elem_spec(nums: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 0 { 0 }
        else {
            let prev = Self::max_elem_spec(nums, end - 1);
            if nums[end - 1] as int > prev { nums[end - 1] as int } else { prev }
        }
    }

    fn can_split(nums: &Vec<i32>, k: i32, max_sum: i64) -> (result: bool)
        requires
            nums.len() >= 1,
            nums.len() <= 1_000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
            k >= 1,
            0 <= max_sum <= 1_000_000_000i64,
        ensures
            result == (Self::greedy_count_spec(nums@, max_sum as int, 0, 0) <= k as int),
    {
        let mut count: i32 = 1;
        let mut current_sum: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            if current_sum + nums[i] as i64 > max_sum {
                count += 1;
                current_sum = nums[i] as i64;
            } else {
                current_sum += nums[i] as i64;
            }
            i += 1;
        }
        count <= k
    }

    pub fn split_array(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1_000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
            1 <= k <= 50,
            k <= nums.len(),
        ensures
            exists|cuts: Seq<int>|
                #[trigger] Self::is_valid_split_spec(nums@.len() as int, k as int, cuts)
                && Self::max_segment_sum_spec(nums@, k as int, cuts) == result as int,
            forall|cuts: Seq<int>|
                Self::is_valid_split_spec(nums@.len() as int, k as int, cuts)
                ==> result as int <= #[trigger] Self::max_segment_sum_spec(nums@, k as int, cuts),
    {
        let mut left: i64 = 0;
        let mut right: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i] as i64 > left {
                left = nums[i] as i64;
            }
            right += nums[i] as i64;
            i += 1;
        }
        while left < right {
            let mid = left + (right - left) / 2;
            if Self::can_split(&nums, k, mid) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left as i32
    }
}
} 
