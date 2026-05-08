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

    proof fn strip_trailing_zeros_range(y: nat)
        requires
            y >= 1,
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

    fn lex_next_exec(x: i32, n: i32) -> (y: i32)
        requires
            1 <= n <= 1000000000,
            1 <= x <= n,
        ensures
            y == Self::lex_next(x as int, n as int),
            1 <= y <= n,
    {
        proof {
            Self::lex_next_in_range(x as int, n as int);
        }
        if x <= n / 10 {
            x * 10
        } else if x % 10 != 9 && x + 1 <= n {
            x + 1
        } else {
            Self::strip_trailing_zeros_exec((x / 10) + 1)
        }
    }

    pub fn find_kth_number(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000000000,
            1 <= k <= n,
        ensures
            result as int == Self::spec_find_kth_number(n as int, k as int),
    {
        let mut curr: i32 = 1;
        let mut i: i32 = 1;
        while i < k
            invariant
                1 <= n <= 1000000000,
                1 <= k <= n,
                1 <= i <= k,
                1 <= curr <= n,
                curr as int == Self::lex_elem((i - 1) as nat, n as int),
            decreases k - i,
        {
            curr = Self::lex_next_exec(curr, n);
            i += 1;
        }
        proof {
            assert(i == k);
            assert(curr as int == Self::lex_elem((k - 1) as nat, n as int));
        }
        curr
    }
}

#[cfg(any())]
impl Solution {
    fn count_steps(n: i64, mut curr: i64, mut next: i64) -> (steps: i64) {
        let mut steps: i64 = 0;
        while curr <= n {
            let bound = if next <= n + 1 { next } else { n + 1 };
            steps += bound - curr;
            curr *= 10;
            next *= 10;
        }
        steps
    }

    pub fn find_kth_number(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000000000,
            1 <= k <= n,
        ensures
            result as int == Self::spec_find_kth_number(n as int, k as int),
    {
        let n64 = n as i64;
        let mut k_left = (k - 1) as i64;
        let mut curr: i64 = 1;

        while k_left > 0 {
            let steps = Self::count_steps(n64, curr, curr + 1);
            if steps <= k_left {
                curr += 1;
                k_left -= steps;
            } else {
                curr *= 10;
                k_left -= 1;
            }
        }

        curr as i32
    }
}

}
