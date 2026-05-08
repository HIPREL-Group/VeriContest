use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum(nums: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        spec_sum(nums, lo, hi - 1) + nums[hi - 1] as int
    }
}

pub open spec fn spec_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

impl Solution {
    pub fn left_right_difference(nums: Vec<i32>) -> (answer: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            answer.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==>
                #[trigger] answer[i] == spec_abs(
                    spec_sum(nums@, 0, i) - spec_sum(nums@, i + 1, nums.len() as int)
                ),
    {
        let n = nums.len();
        let mut total_sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total_sum += nums[i] as i64;
            i += 1;
        }
        let mut answer: Vec<i32> = vec![0i32; n];
        let mut left_sum: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            let right_sum: i64 = total_sum - left_sum - nums[j] as i64;
            let diff: i64 = left_sum - right_sum;
            if diff >= 0 {
                answer.set(j, diff as i32);
            } else {
                answer.set(j, (-diff) as i32);
            }
            left_sum += nums[j] as i64;
            j += 1;
        }
        answer
    }
}

} 
