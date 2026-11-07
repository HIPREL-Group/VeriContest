use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
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
        a.len() == b.len() && forall|v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn max_adj_diff(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() <= 1 { 0 }
        else {
            let rest = Self::max_adj_diff(s.drop_last());
            let gap = s.last() as int - s[s.len() - 2] as int;
            if gap > rest { gap } else { rest }
        }
    }

    pub open spec fn x_coords(points: Seq<Vec<i32>>) -> Seq<i32>
        decreases points.len(),
    {
        if points.len() == 0 { Seq::empty() }
        else { Self::x_coords(points.drop_last()).push(points.last()@[0]) }
    }

    pub fn max_width_of_vertical_area(points: Vec<Vec<i32>>) -> (res: i32)
        requires
            2 <= points.len() <= 100_000,
            forall|i: int| #![trigger points@[i]] 0 <= i < points@.len() ==>
                points@[i]@.len() == 2,
            forall|i: int| #![trigger points@[i]] 0 <= i < points@.len() ==>
                0 <= points@[i]@[0] <= 1_000_000_000,
            forall|i: int| #![trigger points@[i]] 0 <= i < points@.len() ==>
                0 <= points@[i]@[1] <= 1_000_000_000,
        ensures
            res >= 0,
            exists|s: Seq<i32>|
                Self::sorted(s)
                && Self::is_perm(s, Self::x_coords(points@))
                && res as int == Self::max_adj_diff(s),
    {
    }
}

}
