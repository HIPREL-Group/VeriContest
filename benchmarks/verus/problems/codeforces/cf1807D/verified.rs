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

pub open spec fn pref_sum(a: Seq<u32>, k: int) -> int
    recommends 0 <= k <= a.len(),
    decreases k,
{
    if k <= 0 { 0int }
    else { pref_sum(a, k - 1) + a[k - 1] as int }
}

proof fn lemma_pref_eq_sumrange(a: Seq<u32>, k: int)
    requires 0 <= k <= a.len(),
    ensures pref_sum(a, k) == sum_range(a, 0, k),
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_pref_eq_sumrange(a, k - 1);
        lemma_sum_range_extend(a, 0, k);
    }
}

proof fn lemma_sum_range_extend(a: Seq<u32>, l: int, r: int)
    requires 0 <= l, l + 1 <= r, r <= a.len(),
    ensures sum_range(a, l, r) == sum_range(a, l, r - 1) + a[r - 1] as int,
    decreases r - l,
{
    if l == r - 1 {
        assert(sum_range(a, l + 1, r) == 0);
        assert(sum_range(a, l, r) == a[l] as int);
        assert(sum_range(a, l, r - 1) == 0);
    } else {
        lemma_sum_range_extend(a, l + 1, r);
    }
}

proof fn lemma_sum_split(a: Seq<u32>, l: int, mid: int, r: int)
    requires 0 <= l <= mid <= r <= a.len(),
    ensures sum_range(a, l, r) == sum_range(a, l, mid) + sum_range(a, mid, r),
    decreases mid - l,
{
    if l >= mid {
    } else {
        lemma_sum_split(a, l + 1, mid, r);
    }
}

proof fn lemma_sum_range_bound(a: Seq<u32>, l: int, r: int, max_val: int)
    requires 0 <= l <= r <= a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] as int <= max_val,
        max_val >= 0,
    ensures 0 <= sum_range(a, l, r),
        sum_range(a, l, r) <= (r - l) * max_val,
    decreases r - l,
{
    if l >= r {
    } else {
        lemma_sum_range_bound(a, l + 1, r, max_val);
        assert(sum_range(a, l, r) == a[l] as int + sum_range(a, l + 1, r));
        assert(a[l] as int <= max_val);
        assert((r - l) * max_val == max_val + (r - l - 1) * max_val) by (nonlinear_arith);
    }
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
        while i < n
            invariant
                1 <= n <= 200_000,
                a.len() == n,
                forall|kk: int| 0 <= kk < a.len() ==> 1 <= #[trigger] a[kk] <= 1_000_000_000,
                0 <= i <= n,
                prefix.len() == i + 1,
                prefix[0] == 0i64,
                forall|j: int| 0 <= j <= i ==> #[trigger] prefix[j] as int == pref_sum(a@, j),
                s as int == pref_sum(a@, i as int),
                s >= 0,
                s <= (i as i64) * 1_000_000_000,
            decreases n - i,
        {
            s += a[i] as i64;
            prefix.push(s);
            i += 1;
        }
        let pref_n: i64 = prefix[n];
        let mut result: Vec<bool> = Vec::with_capacity(q);
        let mut j: usize = 0;
        while j < q
            invariant
                1 <= n <= 200_000,
                1 <= q <= 200_000,
                a.len() == n,
                ls.len() == q,
                rs.len() == q,
                ks.len() == q,
                prefix.len() == n + 1,
                forall|kk: int| 0 <= kk < a.len() ==> 1 <= #[trigger] a[kk] <= 1_000_000_000,
                forall|kk: int| 0 <= kk < ls.len() ==> 1 <= #[trigger] ls[kk] && ls[kk] as int <= rs[kk] as int && rs[kk] as int <= n as int,
                forall|kk: int| 0 <= kk < rs.len() ==> 1 <= #[trigger] rs[kk] && rs[kk] as int <= n as int,
                forall|kk: int| 0 <= kk < ks.len() ==> 1 <= #[trigger] ks[kk] <= 1_000_000_000,
                forall|kk: int| 0 <= kk <= n as int ==> #[trigger] prefix[kk] as int == pref_sum(a@, kk),
                pref_n == prefix[n as int],
                pref_n as int == pref_sum(a@, n as int),
                pref_n >= 0,
                pref_n <= (n as i64) * 1_000_000_000,
                0 <= j <= q,
                result.len() == j,
                forall|i: int| 0 <= i < j as int ==> #[trigger] result[i] == (
                    (sum_range(a@, 0, ls[i] as int - 1) +
                     ks[i] as int * (rs[i] as int - ls[i] as int + 1) +
                     sum_range(a@, rs[i] as int, n as int)) % 2 == 1
                ),
            decreases q - j,
        {
            let l = ls[j] as usize;
            let r = rs[j] as usize;
            let k_val = ks[j] as i64;
            let count: i64 = (r - l + 1) as i64;
            let pref_l_minus_1 = prefix[l - 1];
            let pref_r_v = prefix[r];
            
            
            
            
            proof {
                lemma_pref_eq_sumrange(a@, (l - 1) as int);
                lemma_pref_eq_sumrange(a@, r as int);
                lemma_pref_eq_sumrange(a@, n as int);
                lemma_sum_split(a@, 0, r as int, n as int);
                
                assert(forall|i: int| 0 <= i < a@.len() ==> #[trigger] a@[i] as int <= 1_000_000_000) by {
                    assert(forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000);
                };
                lemma_sum_range_bound(a@, 0, n as int, 1_000_000_000);
                lemma_sum_range_bound(a@, 0, r as int, 1_000_000_000);
                lemma_sum_range_bound(a@, r as int, n as int, 1_000_000_000);
                lemma_sum_range_bound(a@, 0, (l - 1) as int, 1_000_000_000);
            }
            let outside: i64 = pref_l_minus_1 + (pref_n - pref_r_v);
            assert(k_val * count <= 1_000_000_000i64 * 200_000i64) by (nonlinear_arith)
                requires 0 <= k_val <= 1_000_000_000, 0 <= count <= 200_000;
            assert(k_val * count >= 0) by (nonlinear_arith)
                requires 0 <= k_val, 0 <= count;
            let mid: i64 = k_val * count;
            let total: i64 = outside + mid;
            let answer: bool = total % 2 == 1;
            proof {
                let l_int = l as int;
                let r_int = r as int;
                let count_int = r_int - l_int + 1;
                let k_int = k_val as int;
                let s_lm1 = sum_range(a@, 0, (l - 1) as int);
                let s_r_n = sum_range(a@, r_int, n as int);
                let s_total = sum_range(a@, 0, n as int);
                let s_0r = sum_range(a@, 0, r_int);
                assert(s_total == s_0r + s_r_n);
                assert(pref_l_minus_1 as int == s_lm1);
                assert(pref_r_v as int == s_0r);
                assert(pref_n as int == s_total);
                assert(outside as int == s_lm1 + s_total - s_0r);
                assert(outside as int == s_lm1 + s_r_n);
                assert(mid as int == k_int * count_int);
                assert(total as int == s_lm1 + k_int * count_int + s_r_n);
            }
            result.push(answer);
            j += 1;
        }
        result
    }
}

}
