use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_div6(s: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 0 { 0 }
        else {
            Self::count_div6(s, end - 1) + if s[end - 1] as int % 6 == 0 { 1int } else { 0int }
        }
    }

    pub open spec fn sum_div6(s: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 0 { 0 }
        else {
            Self::sum_div6(s, end - 1) + if s[end - 1] as int % 6 == 0 { s[end - 1] as int } else { 0int }
        }
    }

    pub fn average_value(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result >= 0,
            Self::count_div6(nums@, nums.len() as int) == 0 ==> result == 0,
            Self::count_div6(nums@, nums.len() as int) > 0 ==> result as int == Self::sum_div6(nums@, nums.len() as int) / Self::count_div6(nums@, nums.len() as int),
    {
        let n = nums.len();
        let mut sum: i32 = 0;
        let mut cnt: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let v = nums[i];
            if v > 0 && v % 6 == 0 {
                cnt = cnt + 1;
                sum = sum + v;
            }
            i = i + 1;
        }

        if cnt == 0 {
            0
        } else {
            sum / cnt
        }
    }
}

}
