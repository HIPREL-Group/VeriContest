use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn bid_count_upto(a: Seq<i32>, upto: int, v: int) -> int
    decreases upto,
{
    if upto <= 0 {
        0int
    } else {
        (if a[upto - 1] as int == v { 1int } else { 0int }) + bid_count_upto(a, upto - 1, v)
    }
}

pub open spec fn bid_count(a: Seq<i32>, v: int) -> int {
    bid_count_upto(a, a.len() as int, v)
}

impl Solution {
    pub fn unique_bid_winner(a: Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= a.len() as int,
        ensures
            result == -1 <==> forall|v: int|
                1 <= v <= a.len() as int ==> #[trigger] bid_count(a@, v) != 1,
            result != -1 ==> (
                1 <= (result as int) && (result as int) <= a.len() as int
                && bid_count(a@, a@[(result - 1) as int] as int) == 1
                && forall|v: int|
                    1 <= v <= a.len() as int && bid_count(a@, v) == 1
                        ==> a@[(result - 1) as int] as int <= v
            ),
    {
    }
}

}
