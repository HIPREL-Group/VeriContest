use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn left_run_len_from(s: Seq<i64>, i: int) -> int
    decreases s.len() - i
{
    if i >= s.len() || s[i] != s[0] {
        i
    } else {
        left_run_len_from(s, i + 1)
    }
}

pub open spec fn left_run_len(s: Seq<i64>) -> int {
    left_run_len_from(s, 0)
}

pub open spec fn right_run_len_from(s: Seq<i64>, k: int) -> int
    decreases s.len() - k
{
    if k >= s.len() || s[s.len() - 1 - k] != s[s.len() - 1] {
        k
    } else {
        right_run_len_from(s, k + 1)
    }
}

pub open spec fn right_run_len(s: Seq<i64>) -> int {
    right_run_len_from(s, 0)
}

pub open spec fn min_int(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn expected_min_cost(s: Seq<i64>) -> int {
    let n = s.len() as int;
    let left = left_run_len(s);
    let right = right_run_len(s);
    if s[0] == s[n - 1] {
        let keep = if left + right <= n { left + right } else { n };
        n - keep
    } else {
        min_int(n - left, n - right)
    }
}

pub struct Solution;

impl Solution {
    pub fn min_cost_make_equal(a: Vec<i64>) -> (res: i64)
        requires
            1 <= a.len() <= 200000,
        ensures
            res >= 0,
            res as int == expected_min_cost(a@),
    {
    }
}

}
