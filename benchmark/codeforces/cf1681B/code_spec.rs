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
        while i < m {
            let bi = b[i];
            let s_old: i64 = idx + bi;
            let new_idx: i64 = if s_old >= n_i64 { s_old - n_i64 } else { s_old };
            idx = new_idx;
            i = i + 1;
        }
        a[idx as usize]
    }
}

}
