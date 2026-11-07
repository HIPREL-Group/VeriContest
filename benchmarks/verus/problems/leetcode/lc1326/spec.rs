use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tap_left(ranges: Seq<i32>, t: int) -> int {
        t - ranges[t] as int
    }

    pub open spec fn tap_right(ranges: Seq<i32>, t: int) -> int {
        t + ranges[t] as int
    }

    pub open spec fn is_valid_covering(ranges: Seq<i32>, n: int, sel: Seq<int>) -> bool {
        sel.len() >= 1
        && (forall |k: int| 0 <= k < sel.len() ==> 0 <= #[trigger] sel[k] < ranges.len())
        && Self::tap_left(ranges, sel[0]) <= 0
        && Self::tap_right(ranges, sel[sel.len() - 1 as int]) >= n
        && (forall |k: int|
            #![trigger sel[k]]
            #![trigger sel[k + 1]]
            0 <= k < sel.len() - 1 ==>
            Self::tap_right(ranges, sel[k]) >= Self::tap_left(ranges, sel[k + 1]))
    }

    pub fn min_taps(n: i32, ranges: Vec<i32>) -> (res: i32)
        requires
            1 <= n <= 10_000,
            ranges.len() == n + 1,
            forall |i: int| 0 <= i < ranges.len() ==> 0 <= #[trigger] ranges[i] <= 100,
        ensures
            res == -1 || res >= 1,
            res == -1 ==> forall |sel: Seq<int>|
                !Self::is_valid_covering(ranges@, n as int, sel),
            res >= 1 ==> exists |sel: Seq<int>|
                #[trigger] Self::is_valid_covering(ranges@, n as int, sel)
                && sel.len() == res as nat,
            res >= 1 ==> forall |sel: Seq<int>|
                Self::is_valid_covering(ranges@, n as int, sel)
                ==> sel.len() >= res as nat,
    {
    }
}

}
