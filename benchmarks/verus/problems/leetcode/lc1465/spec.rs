use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
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
        a.len() == b.len() && forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn max_adj_diff(sorted: Seq<i32>, bound: int) -> int
        decreases sorted.len(),
    {
        if sorted.len() == 0 {
            bound
        } else {
            Self::spec_max(
                bound - sorted[sorted.len() - 1] as int,
                Self::max_adj_diff(sorted.drop_last(), sorted[sorted.len() - 1] as int)
            )
        }
    }

    fn find_max_gap(cuts: &Vec<i32>, bound: i32) -> (result: i32)
        requires
            1 <= cuts.len() <= 100_000,
            bound >= 2,
            forall |k: int| 0 <= k < cuts.len() ==> 1 <= #[trigger] cuts[k] < bound,
            forall |k: int, m: int| 0 <= k < m < cuts.len() ==> cuts[k] != cuts[m],
        ensures
            1 <= result < bound,
            exists |sorted: Seq<i32>|
                Self::is_sorted(sorted)
                && Self::is_perm(sorted, cuts@)
                && result as int == Self::max_adj_diff(sorted, bound as int),
    {
    }

    pub fn max_area(h: i32, w: i32, horizontal_cuts: Vec<i32>, vertical_cuts: Vec<i32>) -> (result: i32)
        requires
            2 <= h <= 1_000_000_000,
            2 <= w <= 1_000_000_000,
            1 <= horizontal_cuts.len() <= 100_000,
            1 <= vertical_cuts.len() <= 100_000,
            forall |i: int| 0 <= i < horizontal_cuts.len() ==> 1 <= #[trigger] horizontal_cuts[i] < h,
            forall |j: int| 0 <= j < vertical_cuts.len() ==> 1 <= #[trigger] vertical_cuts[j] < w,
            forall |i: int, j: int| 0 <= i < j < horizontal_cuts.len() ==> horizontal_cuts[i] != horizontal_cuts[j],
            forall |i: int, j: int| 0 <= i < j < vertical_cuts.len() ==> vertical_cuts[i] != vertical_cuts[j],
        ensures
            0 <= result < 1_000_000_007,
            exists |sh: Seq<i32>, sv: Seq<i32>|
                Self::is_sorted(sh)
                && Self::is_perm(sh, horizontal_cuts@)
                && Self::is_sorted(sv)
                && Self::is_perm(sv, vertical_cuts@)
                && result as int == (Self::max_adj_diff(sh, h as int) * Self::max_adj_diff(sv, w as int)) % 1_000_000_007,
    {
    }
}

}
