use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn greedy_count(p: Seq<i64>, n: int, i: int, count: int) -> int
    decreases n - i,
{
    if i + 1 >= n {
        count
    } else if p[i] > p[i + 1] {
        greedy_count(p, n, i + 2, count + 1)
    } else {
        greedy_count(p, n, i + 1, count)
    }
}

impl Solution {
    pub fn max_odd_subarrays(n: usize, p: Vec<i64>) -> (result: usize)
        requires
            1 <= n <= 100000,
            p.len() == n,
            forall|i: int| 0 <= i < p.len() ==> 1 <= #[trigger] p[i] <= n as i64,
        ensures
            result as int == greedy_count(p@, n as int, 0, 0),
    {
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i + 1 < n {
            if p[i] > p[i + 1] {
                count += 1;
                i += 2;
            } else {
                i += 1;
            }
        }
        count
    }
}

}
