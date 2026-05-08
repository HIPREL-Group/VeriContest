use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min(a: int, b: int) -> int {
        if a < b {
            a
        } else {
            b
        }
    }

    pub fn max_area(height: Vec<i32>) -> (result: i32)
        requires
            2 <= height.len() <= 100_000,
            forall|i: int| 0 <= i < height.len() ==> 0 <= #[trigger] height[i] <= 10_000,
        ensures
            forall|i: int, j: int|
                0 <= i < j < height.len() ==> result as int >= (j - i) * Solution::min(
                    height[i] as int,
                    height[j] as int,
                ),
            exists|i: int, j: int|
                0 <= i < j < height.len() && result as int == (j - i) * Solution::min(
                    height[i] as int,
                    height[j] as int,
                ),
    {
        let n = height.len();
        let mut left: usize = 0;
        let mut right: usize = n - 1;

        let init_width = (right - left) as i32;
        let init_h = if height[left] < height[right] {
            height[left]
        } else {
            height[right]
        };

        let mut max_area: i32 = init_width * init_h;

        while left < right {
            let cur_left = left;
            let cur_right = right;

            let width = (cur_right - cur_left) as i32;

            let h = if height[cur_left] < height[cur_right] {
                height[cur_left]
            } else {
                height[cur_right]
            };

            let area = width * h;

            if area > max_area {
                max_area = area;
            }

            if height[cur_left] <= height[cur_right] {
                left += 1;
            } else {
                right -= 1;
            }
        }

        max_area
    }
}

} 
