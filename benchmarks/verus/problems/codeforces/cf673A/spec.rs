use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn GAME_LEN() -> int {
    90
}

pub open spec fn int_min(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

pub open spec fn spec_prefix_candidate(t: Seq<i32>) -> int {
    if t.len() >= 1 && t[0] >= 16 {
        15
    } else {
        90
    }
}

pub open spec fn spec_gap_candidate(t: Seq<i32>, i: int) -> int {
    if 0 <= i && i < t.len() - 1 && t[i + 1] - t[i] - 1 >= 15 {
        t[i] + 15
    } else {
        90
    }
}

pub open spec fn spec_min_gaps_from(t: Seq<i32>, i: int) -> int
    recommends
        0 <= i <= t.len() - 1,
    decreases ((t.len() - 1) - i) as nat,
{
    if i >= t.len() - 1 {
        90
    } else {
        int_min(spec_gap_candidate(t, i), spec_min_gaps_from(t, i + 1))
    }
}

pub open spec fn spec_suffix_candidate(t: Seq<i32>) -> int {
    if t.len() >= 1 && GAME_LEN() - t[t.len() - 1] >= 15 {
        t[t.len() - 1] + 15
    } else {
        90
    }
}

pub open spec fn watch_spec(t: Seq<i32>) -> int {
    int_min(
        int_min(
            int_min(90, spec_prefix_candidate(t)),
            spec_min_gaps_from(t, 0),
        ),
        spec_suffix_candidate(t),
    )
}

impl Solution {
    pub fn fold_gaps(t: &Vec<i32>, i: usize, acc: i32) -> (r: i32)
        requires
            1 <= t.len() && t.len() <= 90,
            i <= t.len() - 1,
            forall|k: int| 0 <= k < t.len() ==> 1 <= #[trigger] t[k] && t[k] <= 90,
            forall|a: int, b: int|
                0 <= a < b < t.len() ==> #[trigger] t[a] < #[trigger] t[b],
        ensures
            r as int == int_min(acc as int, spec_min_gaps_from(t@, i as int)),
    {
    }

    pub fn watch_minutes(t: Vec<i32>) -> (result: i32)
        requires
            1 <= t.len() && t.len() <= 90,
            forall|k: int| 0 <= k < t.len() ==> 1 <= #[trigger] t[k] && t[k] <= 90,
            forall|a: int, b: int|
                0 <= a < b < t.len() ==> #[trigger] t[a] < #[trigger] t[b],
        ensures
            result as int == watch_spec(t@),
    {
    }
}

}
