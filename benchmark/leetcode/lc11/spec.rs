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
    }
}

} 
