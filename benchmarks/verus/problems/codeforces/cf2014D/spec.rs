use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_overlaps_window(start: int, d: int, l: int, r: int) -> bool {
        start <= r && l <= start + d - 1
    }

    pub open spec fn spec_overlap_count_prefix(start: int, d: int, left: Seq<i32>, right: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto <= left.len(),
            left.len() == right.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::spec_overlap_count_prefix(start, d, left, right, upto - 1)
                + if Self::spec_overlaps_window(start, d, left[upto - 1] as int, right[upto - 1] as int) {
                    1int
                } else {
                    0int
                }
        }
    }

    pub open spec fn spec_overlap_count(start: int, d: int, left: Seq<i32>, right: Seq<i32>) -> int
        recommends
            left.len() == right.len(),
    {
        Self::spec_overlap_count_prefix(start, d, left, right, left.len() as int)
    }

    pub fn best_start_days(n: i32, d: i32, left: Vec<i32>, right: Vec<i32>) -> (res: (i32, i32))
        requires
            1 <= n,
            n <= 100000,
            1 <= d <= n,
            1 <= left.len() <= n as nat,
            left.len() == right.len(),
            forall|j: int| 0 <= j < left.len() as int ==> 1 <= #[trigger] left[j] <= right[j] <= n,
        ensures
            1 <= res.0 <= n - d + 1,
            1 <= res.1 <= n - d + 1,
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    ==> Self::spec_overlap_count(res.0 as int, d as int, left@, right@)
                        >= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@),
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    ==> Self::spec_overlap_count(res.1 as int, d as int, left@, right@)
                        <= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@),
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                        == Self::spec_overlap_count(res.0 as int, d as int, left@, right@)
                    ==> res.0 as int <= s,
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                        == Self::spec_overlap_count(res.1 as int, d as int, left@, right@)
                    ==> res.1 as int <= s,
    {
    }
}

}
