use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_additional_from(flowerbed: Seq<i32>, i: int, prev_planted: bool) -> int
        decreases flowerbed.len() - i,
    {
        if i >= flowerbed.len() {
            0
        } else if flowerbed[i] == 1 {
            Self::max_additional_from(flowerbed, i + 1, true)
        } else {
            let next_empty = i + 1 >= flowerbed.len() || flowerbed[i + 1] == 0;
            if !prev_planted && next_empty {
                1 + Self::max_additional_from(flowerbed, i + 1, true)
            } else {
                Self::max_additional_from(flowerbed, i + 1, false)
            }
        }
    }

    pub fn can_place_flowers(flowerbed: Vec<i32>, n: i32) -> (res: bool)
        requires
            1 <= flowerbed.len() <= 20_000,
            forall |i: int| 0 <= i < flowerbed.len() ==> (#[trigger] flowerbed[i] == 0 || flowerbed[i] == 1),
            forall |i: int| 0 <= i < flowerbed.len() - 1 ==> !(#[trigger] flowerbed[i] == 1 && flowerbed[i + 1] == 1),
            0 <= n <= flowerbed.len(),
        ensures
            res == (n as int <= Self::max_additional_from(flowerbed@, 0, false)),
    {
        
    }
}

}
