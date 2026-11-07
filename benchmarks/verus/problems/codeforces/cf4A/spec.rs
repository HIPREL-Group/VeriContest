use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn can_split_even(w: u32) -> (res: bool)
        requires
            1 <= w <= 100,
        ensures
            res == (w >= 4 && w % 2 == 0),
    {
    }
}

}
