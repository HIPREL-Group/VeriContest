use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn gen(k: int) -> int
    decreases k
{
    if k <= 0 { 0 }
    else if k == 1 { 1 }
    else if k % 2 == 0 { gen(k / 2) }
    else { gen(k / 2) + gen(k / 2 + 1) }
}

impl Solution {
    pub fn get_maximum_generated(n: i32) -> (result: i32)
        requires
            0 <= n <= 100,
        ensures
            forall|k: int| 0 <= k <= n as int ==> result as int >= #[trigger] gen(k),
            exists|k: int| 0 <= k <= n as int && result as int == #[trigger] gen(k),
    {
    }
}

}
