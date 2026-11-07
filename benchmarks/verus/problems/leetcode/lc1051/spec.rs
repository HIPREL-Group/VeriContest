use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    pub open spec fn is_perm_of(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && forall |v: i32| Self::count(a, v) == Self::count(b, v)
    }

    pub open spec fn mismatch_count(a: Seq<i32>, b: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            (if a[end - 1] != b[end - 1] { 1int } else { 0int }) + Self::mismatch_count(a, b, end - 1)
        }
    }

    pub fn height_checker(heights: Vec<i32>) -> (res: i32)
        requires
            1 <= heights.len() <= 100,
            forall |i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 100,
        ensures
            exists |expected: Seq<i32>| #[trigger] expected.len() == heights@.len()
                && Self::is_sorted(expected)
                && Self::is_perm_of(expected, heights@)
                && res as int == Self::mismatch_count(heights@, expected, heights@.len() as int),
    {
    }
}

}
