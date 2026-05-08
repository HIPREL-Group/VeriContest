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


proof fn lemma_greedy_count_offset(p: Seq<i64>, n: int, i: int, c1: int, c2: int)
    requires
        0 <= i,
        0 <= n,
    ensures
        greedy_count(p, n, i, c1 + c2) == greedy_count(p, n, i, c1) + c2,
    decreases n - i,
{
    if i + 1 >= n {
    } else if p[i] > p[i + 1] {
        lemma_greedy_count_offset(p, n, i + 2, c1 + 1, c2);
    } else {
        lemma_greedy_count_offset(p, n, i + 1, c1, c2);
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
        while i + 1 < n
            invariant
                0 <= i,
                i <= n,
                n == p.len(),
                1 <= n <= 100000,
                count as int + greedy_count(p@, n as int, i as int, 0) == greedy_count(p@, n as int, 0, 0),
                count <= i,
                count <= n,
            decreases n - i,
        {
            if p[i] > p[i + 1] {
                proof {
                    
                    
                    lemma_greedy_count_offset(p@, n as int, i as int + 2, 0, 1);
                }
                count += 1;
                i += 2;
            } else {
                i += 1;
            }
        }
        proof {
            
            assert(greedy_count(p@, n as int, i as int, 0) == 0);
        }
        count
    }
}

}
