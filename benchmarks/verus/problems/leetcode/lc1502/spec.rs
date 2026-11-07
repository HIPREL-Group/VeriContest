use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_sorted_seq(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn is_ap(s: Seq<i32>) -> bool {
        s.len() <= 1 || forall |i: int| 0 <= i < s.len() - 1 ==>
            s[i + 1] as int - (#[trigger] s[i]) as int == s[1] as int - s[0] as int
    }

    pub open spec fn can_form_ap(s: Seq<i32>) -> bool {
        exists |sorted: Seq<i32>|
            sorted.len() == s.len() &&
            Self::is_sorted_seq(sorted) &&
            Self::is_perm(s, sorted) &&
            Self::is_ap(sorted)
    }

    pub fn can_make_arithmetic_progression(arr: Vec<i32>) -> (res: bool)
        requires
            2 <= arr.len() <= 1000,
            forall |i: int| 0 <= i < arr.len() ==>
                -1_000_000 <= #[trigger] arr[i] <= 1_000_000,
        ensures
            res == Self::can_form_ap(arr@),
    {
    }
}

}
