use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_color(c: int) -> bool {
        c == 0 || c == 1 || c == 2
    }

    pub open spec fn segment_non_white(s: Seq<i32>, l: int, r: int) -> bool {
        forall|k: int| l <= k < r ==> #[trigger] s[k] != 0
    }

    pub open spec fn segment_has_color(s: Seq<i32>, l: int, r: int, color: int) -> bool {
        exists|k: int| l <= k < r && s[k] as int == color
    }

    pub open spec fn good_segment(s: Seq<i32>, l: int, r: int) -> bool {
        0 <= l < r <= s.len()
            && (l == 0 || s[l - 1] == 0)
            && (r == s.len() || s[r] == 0)
            && Self::segment_non_white(s, l, r)
    }

    pub open spec fn valid_picture(s: Seq<i32>) -> bool {
        forall|l: int, r: int|
            Self::good_segment(s, l, r)
                ==> Self::segment_has_color(s, l, r, 1)
                    && Self::segment_has_color(s, l, r, 2)
    }

    pub fn possible_picture(cells: Vec<i32>) -> (res: bool)
        requires
            1 <= cells.len() <= 100000,
            forall|k: int| 0 <= k < cells.len() as int ==> Self::is_color(#[trigger] cells[k] as int),
        ensures
            res == Self::valid_picture(cells@),
    {
    }
}

}
