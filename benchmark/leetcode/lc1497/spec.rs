use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn remainder_count(arr: Seq<i32>, k: int, r: int) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else if arr.last() as int % k == r {
        1 + remainder_count(arr.drop_last(), k, r)
    } else {
        remainder_count(arr.drop_last(), k, r)
    }
}

impl Solution {
    pub fn can_arrange(arr: Vec<i32>, k: i32) -> (result: bool)
        requires
            arr@.len() % 2 == 0,
            2 <= arr@.len() <= 100000,
            1 <= k <= 100000,
            forall|i: int| 0 <= i < arr@.len() ==> -1000000000 <= #[trigger] arr@[i] <= 1000000000,
        ensures
            result == (remainder_count(arr@, k as int, 0) % 2 == 0 && forall|r: int|
                1 <= r < k as int ==> #[trigger] remainder_count(arr@, k as int, r)
                    == remainder_count(arr@, k as int, k as int - r)),
    {
    }
}

}
