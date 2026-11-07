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

    proof fn strip_trailing_zeros_range(y: nat)
        requires y >= 1,
        ensures
            1 <= Self::strip_trailing_zeros(y) <= y,
        decreases y,
    {
        if y % 10 == 0 && y != 0 {
            Self::strip_trailing_zeros_range((y / 10) as nat);
        }
    }

    proof fn lex_next_in_range(x: int, n: int)
        requires
            1 <= n,
            1 <= x <= n,
        ensures
            1 <= Self::lex_next(x, n) <= n,
    {
        if x * 10 <= n {
        } else if x % 10 != 9 && x + 1 <= n {
        } else {
            Self::strip_trailing_zeros_range(((x / 10) + 1) as nat);
        }
    }

    pub fn lexical_order(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 50_000,
        ensures
            result.len() == n as nat,
            result@ == Self::lex_sequence(n as nat),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut curr: i32 = 1;
        let mut i: i32 = 0;
        while i < n
            invariant
                1 <= n <= 50_000,
                0 <= i <= n,
                result.len() == i as nat,
                forall |j: int| 0 <= j < i ==> result[j] as int == Self::lex_elem(j as nat, n as int),
                curr as int == Self::lex_elem(i as nat, n as int),
                1 <= curr <= n,
            decreases n - i,
        {
            result.push(curr);
            curr = Self::lex_next_exec(curr, n);
            i += 1;
            proof {
                assert(result.len() == i as nat);
                assert(forall |j: int| 0 <= j < i ==> result[j] as int == Self::lex_elem(j as nat, n as int));
                assert(curr as int == Self::lex_elem(i as nat, n as int));
            }
        }
        result
    }

    fn lex_next_exec(x: i32, n: i32) -> (y: i32)
        requires
            1 <= n <= 50_000,
            1 <= x <= n,
        ensures
            y == Self::lex_next(x as int, n as int),
            1 <= y <= n,
    {
        proof { Self::lex_next_in_range(x as int, n as int); }
        if x * 10 <= n {
            x * 10
        } else if x % 10 != 9 && x + 1 <= n {
            x + 1
        } else {
            Self::strip_trailing_zeros_exec((x / 10) + 1)
        }
    }

    fn strip_trailing_zeros_exec(mut y: i32) -> (z: i32)
        requires
            y >= 1,
        ensures
            z as int == Self::strip_trailing_zeros(y as nat) as int,
    {
        let ghost init = y;
        while y % 10 == 0 && y != 0
            invariant
                y >= 0,
                Self::strip_trailing_zeros(y as nat) == Self::strip_trailing_zeros(init as nat),
            decreases y,
        {
            y = y / 10;
        }
        y
    }
}

}
