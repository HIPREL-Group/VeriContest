use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn final_idx(n: int, b: Seq<i64>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        let prev = final_idx(n, b, k - 1);
        let s = prev + b[k - 1] as int;
        if s >= n { s - n } else { s }
    }
}

proof fn lemma_final_idx_bounds(n: int, b: Seq<i64>, k: int)
    requires
        n >= 2,
        0 <= k <= b.len(),
        forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] as int <= n - 1,
    ensures
        0 <= final_idx(n, b, k) < n,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_final_idx_bounds(n, b, k - 1);
    }
}

impl Solution {
    pub fn top_card(n: usize, a: Vec<i64>, m: usize, b: Vec<i64>) -> (result: i64)
        requires
            2 <= n <= 200000,
            1 <= m <= 200000,
            a.len() == n,
            b.len() == m,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= n as i64,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= n as i64 - 1,
        ensures
            result as int == a[final_idx(n as int, b@, m as int)] as int,
    {
        let n_i64 = n as i64;
        let mut idx: i64 = 0;
        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i <= m,
                n_i64 == n as i64,
                m == b.len(),
                a.len() == n,
                2 <= n <= 200000,
                forall|k: int| 0 <= k < b.len() ==> 1i64 <= #[trigger] b[k] <= n as i64 - 1i64,
                0 <= idx < n_i64,
                idx as int == final_idx(n as int, b@, i as int),
            decreases m - i,
        {
            let bi = b[i];
            assert(1 <= bi <= n_i64 - 1);
            let s_old: i64 = idx + bi;
            assert(1 <= s_old <= 2 * n_i64 - 2);
            let new_idx: i64 = if s_old >= n_i64 { s_old - n_i64 } else { s_old };
            assert(0 <= new_idx < n_i64);
            
            
            
            
            idx = new_idx;
            i = i + 1;
        }
        a[idx as usize]
    }
}

}
