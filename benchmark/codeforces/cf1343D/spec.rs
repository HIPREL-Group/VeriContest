use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn pair_cost(ai: i64, aj: i64, k: i64, x: i64) -> int {
    if ai + aj == x { 0 }
    else if x >= ({let lo = if ai < aj { ai } else { aj }; lo} + 1) &&
            x <= ({let hi = if ai > aj { ai } else { aj }; hi} + k) { 1 }
    else { 2 }
}

pub open spec fn total_cost_rec(a: Seq<i64>, n: usize, k: i64, x: i64, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else {
        total_cost_rec(a, n, k, x, end - 1)
          + pair_cost(a[end - 1], a[n as int - end], k, x)
    }
}

pub open spec fn total_cost(a: Seq<i64>, n: usize, k: i64, x: i64) -> int {
    total_cost_rec(a, n, k, x, (n / 2) as int)
}

pub struct Solution;

impl Solution {
    pub fn constant_palindrome_sum(n: usize, k: i64, a: Vec<i64>) -> (ans: i64)
        requires
            2 <= n && n <= 200000,
            n % 2 == 0,
            1 <= k && k <= 200000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= k,
        ensures
            0 <= ans && ans <= n as i64,
            forall|x: i64| 2 <= x && x <= 2 * k ==>
                ans as int <= total_cost(a@, n, k, x),
            exists|x: i64| 2 <= x && x <= 2 * k && ans as int == total_cost(a@, n, k, x),
    {
    }
}

}
