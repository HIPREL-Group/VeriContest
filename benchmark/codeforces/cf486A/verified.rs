use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn f_value(n: int) -> int
    decreases n,
{
    if n <= 0 {
        0int
    } else if n % 2 == 0 {
        f_value(n - 1) + n
    } else {
        f_value(n - 1) - n
    }
}

proof fn lemma_f_value(n: int)
    requires
        n >= 0,
    ensures
        n % 2 == 0 ==> f_value(n) == n / 2,
        n % 2 != 0 ==> f_value(n) == -((n + 1) / 2),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_f_value(n - 1);
    }
}

impl Solution {
    pub fn calculating_function(n: i64) -> (result: i64)
        requires
            1 <= n <= 1000000000000000,
        ensures
            result as int == f_value(n as int),
    {
        proof {
            lemma_f_value(n as int);
        }
        if n % 2 == 0 {
            n / 2
        } else {
            -((n + 1) / 2)
        }
    }
}

}
