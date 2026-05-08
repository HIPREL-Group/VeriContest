use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn triple_product(nums: Seq<i32>, i: int, j: int, k: int) -> int
        recommends
            0 <= i < j < k < nums.len(),
    {
        nums[i] as int * nums[j] as int * nums[k] as int
    }

    pub fn maximum_product(nums: Vec<i32>) -> (result: i32)
        requires
            nums.len() >= 3,
            forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            exists|i: int, j: int, k: int|
                0 <= i < j < k < nums.len()
                && result as int == #[trigger] Self::triple_product(nums@, i, j, k),
            forall|i: int, j: int, k: int|
                0 <= i < j < k < nums.len()
                ==> #[trigger] Self::triple_product(nums@, i, j, k) <= result as int,
    {
        let n = nums.len();
        let mut top1: i32 = i32::MIN;
        let mut top2: i32 = i32::MIN;
        let mut top3: i32 = i32::MIN;
        let mut bot1: i32 = i32::MAX;
        let mut bot2: i32 = i32::MAX;

        let mut i = 0usize;
        while i < n
        {
            let v = nums[i];

            if v >= top1 {
                top3 = top2;
                top2 = top1;
                top1 = v;
            } else if v >= top2 {
                top3 = top2;
                top2 = v;
            } else if v >= top3 {
                top3 = v;
            }

            if v <= bot1 {
                bot2 = bot1;
                bot1 = v;
            } else if v <= bot2 {
                bot2 = v;
            }
            i += 1;
        }

        let p1 = top1 as i64 * top2 as i64 * top3 as i64;
        let p2 = bot1 as i64 * bot2 as i64 * top1 as i64;
        let best = if p1 >= p2 { p1 } else { p2 };

        best as i32
    }
}

}
