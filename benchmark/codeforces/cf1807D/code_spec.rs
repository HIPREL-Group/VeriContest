use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_range(a: Seq<u32>, l: int, r: int) -> int
    recommends 0 <= l <= r <= a.len(),
    decreases r - l,
{
    if l >= r { 0int }
    else { a[l] as int + sum_range(a, l + 1, r) }
}

impl Solution {
    pub fn odd_queries(
        a: Vec<u32>,
        n: usize,
        ls: Vec<u32>,
        rs: Vec<u32>,
        ks: Vec<u32>,
        q: usize,
    ) -> (result: Vec<bool>)
        requires
            1 <= n <= 200_000,
            1 <= q <= 200_000,
            a.len() == n,
            ls.len() == q,
            rs.len() == q,
            ks.len() == q,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] && ls[i] as int <= rs[i] as int && rs[i] as int <= n as int,
            forall|i: int| 0 <= i < rs.len() ==> 1 <= #[trigger] rs[i] && rs[i] as int <= n as int,
            forall|i: int| 0 <= i < ks.len() ==> 1 <= #[trigger] ks[i] <= 1_000_000_000,
        ensures
            result.len() == q,
            forall|i: int| 0 <= i < q ==> #[trigger] result[i] == (
                (sum_range(a@, 0, ls[i] as int - 1) +
                 ks[i] as int * (rs[i] as int - ls[i] as int + 1) +
                 sum_range(a@, rs[i] as int, n as int)) % 2 == 1
            ),
    {
        let mut prefix: Vec<i64> = Vec::with_capacity(n + 1);
        prefix.push(0i64);
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            s += a[i] as i64;
            prefix.push(s);
            i += 1;
        }
        let pref_n: i64 = prefix[n];
        let mut result: Vec<bool> = Vec::with_capacity(q);
        let mut j: usize = 0;
        while j < q {
            let l = ls[j] as usize;
            let r = rs[j] as usize;
            let k_val = ks[j] as i64;
            let count: i64 = (r - l + 1) as i64;
            let pref_l_minus_1 = prefix[l - 1];
            let pref_r_v = prefix[r];
            let outside: i64 = pref_l_minus_1 + (pref_n - pref_r_v);
            let mid: i64 = k_val * count;
            let total: i64 = outside + mid;
            let answer: bool = total % 2 == 1;
            result.push(answer);
            j += 1;
        }
        result
    }
}

}
