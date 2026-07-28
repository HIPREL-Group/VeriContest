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
    #[verifier::exec_allows_no_decreases_clause]
    fn build_tables(n: usize, k: i64, a: &Vec<i64>) -> (res: (Vec<i64>, Vec<i64>))
        requires
            2 <= n && n <= 200000,
            n % 2 == 0,
            1 <= k && k <= 200000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= k,
        ensures
            res.0.len() == (2 * k + 2) as usize,
            res.1.len() == (2 * k + 2) as usize,
    {
        let half = n / 2;
        let size = (2 * k + 2) as usize;
        let mut diff: Vec<i64> = Vec::new();
        let mut exact: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < size {
            diff.push(0);
            exact.push(0);
            idx = idx + 1;
        }
        let mut i: usize = 0;
        while i < half {
            let ai = a[i];
            let aj = a[n - 1 - i];
            let lo = if ai < aj { ai } else { aj };
            let hi = if ai > aj { ai } else { aj };
            let left = (lo + 1) as usize;
            let right_plus_one = (hi + k + 1) as usize;
            let sum = (ai + aj) as usize;
            diff.set(left, diff[left] + 1);
            diff.set(right_plus_one, diff[right_plus_one] - 1);
            exact.set(sum, exact[sum] + 1);
            i = i + 1;
        }
        (diff, exact)
    }

    #[verifier::exec_allows_no_decreases_clause]
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
        let tables = Solution::build_tables(n, k, &a);
        let diff = tables.0;
        let exact = tables.1;
        let mut ans = n as i64;
        let mut cover: i64 = 0;
        let mut x: usize = 2;
        let limit = (2 * k) as usize;
        while x <= limit {
            cover = cover + diff[x];
            let cost = n as i64 - cover - exact[x];
            if cost < ans {
                ans = cost;
            }
            x = x + 1;
        }
        ans
    }
}

}
