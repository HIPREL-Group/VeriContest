use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn stable_prefix(height: Seq<i32>, threshold: i32, i: int) -> Seq<i32>
        recommends
            1 <= i <= height.len(),
        decreases i
    {
        if i <= 1 {
            seq![]
        } else {
            let prev = Self::stable_prefix(height, threshold, i - 1);
            if height[i - 2] > threshold {
                prev.push((i - 1) as i32)
            } else {
                prev
            }
        }
    }

    pub fn stable_mountains(height: Vec<i32>, threshold: i32) -> (result: Vec<i32>)
        requires
            2 <= height.len() <= 100,
            forall|j: int| 0 <= j < height.len() ==> #[trigger] height[j] >= 1,
            forall|j: int| 0 <= j < height.len() ==> #[trigger] height[j] <= 100,
            1 <= threshold <= 100,
        ensures
            result@ == Self::stable_prefix(height@, threshold, height@.len() as int),
    {
    }
}

}
