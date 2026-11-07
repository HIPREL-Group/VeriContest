use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_l_prefix(l: Seq<i64>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if len == 1 {
        l[0] as int
    } else {
        let m = max_l_prefix(l, len - 1);
        let v = l[len - 1] as int;
        if v > m {
            v
        } else {
            m
        }
    }
}

pub open spec fn max_l_suffix(l: Seq<i64>, j: int, n: int) -> int
    decreases n - j,
{
    if j >= n {
        0int
    } else if j + 1 == n {
        l[j] as int
    } else {
        let m = max_l_suffix(l, j + 1, n);
        let v = l[j] as int;
        if v > m {
            v
        } else {
            m
        }
    }
}

pub open spec fn min_r_prefix(r: Seq<i64>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if len == 1 {
        r[0] as int
    } else {
        let m = min_r_prefix(r, len - 1);
        let v = r[len - 1] as int;
        if v < m {
            v
        } else {
            m
        }
    }
}

pub open spec fn min_r_suffix(r: Seq<i64>, j: int, n: int) -> int
    decreases n - j,
{
    if j >= n {
        0int
    } else if j + 1 == n {
        r[j] as int
    } else {
        let m = min_r_suffix(r, j + 1, n);
        let v = r[j] as int;
        if v < m {
            v
        } else {
            m
        }
    }
}

pub open spec fn max_l_excluding(l: Seq<i64>, n: int, k: int) -> int {
    if k == 0 {
        max_l_suffix(l, 1, n)
    } else if k == n - 1 {
        max_l_prefix(l, n - 1)
    } else {
        let a = max_l_prefix(l, k);
        let b = max_l_suffix(l, k + 1, n);
        if a > b {
            a
        } else {
            b
        }
    }
}

pub open spec fn min_r_excluding(r: Seq<i64>, n: int, k: int) -> int {
    if k == 0 {
        min_r_suffix(r, 1, n)
    } else if k == n - 1 {
        min_r_prefix(r, n - 1)
    } else {
        let a = min_r_prefix(r, k);
        let b = min_r_suffix(r, k + 1, n);
        if a < b {
            a
        } else {
            b
        }
    }
}

pub open spec fn intersection_len_excluding(l: Seq<i64>, r: Seq<i64>, n: int, k: int) -> int {
    let ml = max_l_excluding(l, n, k);
    let mr = min_r_excluding(r, n, k);
    if ml > mr {
        0int
    } else {
        mr - ml
    }
}

impl Solution {
    pub fn maximal_intersection_len(l: Vec<i64>, r: Vec<i64>) -> (result: i64)
        requires
            2 <= l.len() <= 300_000,
            l.len() == r.len(),
            forall|i: int|
                0 <= i < l.len() ==> 0 <= #[trigger] l[i] && l[i] <= r[i] && r[i] <= 1_000_000_000,
        ensures
            result >= 0,
            forall|k: int|
                0 <= k < l.len() ==> intersection_len_excluding(l@, r@, l.len() as int, k) <= result as int,
            exists|k: int|
                0 <= k < l.len() && intersection_len_excluding(l@, r@, l.len() as int, k) == result as int,
    {
    }
}

}
