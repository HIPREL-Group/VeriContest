use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_count(y: nat) -> nat
        decreases y,
    {
        if y < 10 {
            1
        } else {
            1 + Self::digit_count((y / 10) as nat)
        }
    }

    pub open spec fn strip_trailing_zeros(y: nat) -> nat
        decreases y,
    {
        if y % 10 == 0 && y != 0 {
            Self::strip_trailing_zeros((y / 10) as nat)
        } else {
            y
        }
    }

    pub open spec fn lex_next(x: int, n: int) -> int
    {
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

    pub open spec fn lex_sequence(n: nat) -> Seq<i32> {
        Seq::new(n, |i: int| Self::lex_elem(i as nat, n as int) as i32)
    }

    pub open spec fn count(s: Seq<i32>, v: i32) -> nat
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1nat } else { 0nat }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    pub fn lexical_order(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 50_000,
        ensures
            result.len() == n as nat,
            result@ == Self::lex_sequence(n as nat),
    {
    }
}

}
