use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn strip_trailing_zeros(y: nat) -> nat
        decreases y,
    {
        if y % 10 == 0 && y != 0 {
            Self::strip_trailing_zeros((y / 10) as nat)
        } else {
            y
        }
    }

    pub open spec fn lex_next(x: int, n: int) -> int {
        if x * 10 <= n {
            x * 10
        } else if x % 10 != 9 && x + 1 <= n {
            x + 1
        } else {
            Self::strip_trailing_zeros(((x / 10) + 1) as nat) as int
        }
    }

    pub open spec fn lex_elem(i: nat, n: int) -> int
        decreases i,
    {
        if i == 0 {
            1
        } else {
            Self::lex_next(Self::lex_elem((i - 1) as nat, n), n)
        }
    }

    pub open spec fn spec_find_kth_number(n: int, k: int) -> int
        recommends
            1 <= k <= n,
            1 <= n,
    {
        Self::lex_elem((k - 1) as nat, n)
    }

    pub fn find_kth_number(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000000000,
            1 <= k <= n,
        ensures
            result as int == Self::spec_find_kth_number(n as int, k as int),
    {
    }
}

}
