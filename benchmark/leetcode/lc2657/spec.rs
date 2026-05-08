use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn in_prefix(s: Seq<i32>, end: int, x: i32) -> bool {
        exists |j: int| 0 <= j < end && #[trigger] s[j] == x
    }

    pub open spec fn count_matches(a: Seq<i32>, b: Seq<i32>, end: int, idx: int) -> int
        recommends
            b.len() == a.len(),
            0 <= end <= a.len(),
            0 <= idx <= end,
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            Self::count_matches(a, b, end, idx - 1)
                + if Self::in_prefix(b, end, a[idx - 1]) { 1int } else { 0int }
        }
    }

    pub open spec fn prefix_common_count(a: Seq<i32>, b: Seq<i32>, end: int) -> int
        recommends
            b.len() == a.len(),
            0 <= end <= a.len(),
    {
        Self::count_matches(a, b, end, end)
    }

    pub fn find_the_prefix_common_array(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= a.len() <= 50,
            b.len() == a.len(),
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= a.len(),
            forall |i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= b.len(),
            forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] != a[j],
            forall |i: int, j: int| 0 <= i < j < b.len() ==> b[i] != b[j],
        ensures
            result.len() == a.len(),
            forall |i: int| 0 <= i < result.len() ==> {
                &&& 0 <= #[trigger] result[i] <= i + 1
                &&& result[i] as int == Self::prefix_common_count(a@, b@, i + 1)
            },
    {
    }
}

}
