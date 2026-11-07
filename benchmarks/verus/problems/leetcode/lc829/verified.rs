use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_valid_k(n: int, k: int) -> bool {
        k >= 1 && n - k * (k - 1) / 2 > 0 && (n - k * (k - 1) / 2) % k == 0
    }

    pub open spec fn count_ways(n: int, bound: int) -> nat
        decreases bound,
    {
        if bound <= 0 {
            0
        } else {
            Self::count_ways(n, bound - 1) + if Self::is_valid_k(n, bound) { 1 as nat } else { 0 as nat }
        }
    }

    proof fn lemma_k_bound(k: int, n: int)
        requires
            n >= 1,
            n <= 1_000_000_000,
            k >= 1,
            k * (k - 1) < 2 * n,
        ensures
            k <= 50_000,
            k <= n,
    {
        if k > 50_000 {
            assert(k * (k - 1) >= 50_001 * 50_000) by(nonlinear_arith)
                requires k > 50_000, k >= 1;
        }
        if k > n {
            assert(k >= n + 1);
            assert(k * (k - 1) >= (n + 1) * n) by(nonlinear_arith)
                requires k >= n + 1, n >= 1;
            assert((n + 1) * n >= 2 * n) by(nonlinear_arith)
                requires n >= 1;
        }
    }

    proof fn lemma_invalid_above(n: int, k: int, j: int)
        requires
            n >= 1,
            k >= 1,
            j >= k,
            k * (k - 1) >= 2 * n,
        ensures
            !Self::is_valid_k(n, j),
    {
        assert(j * (j - 1) >= k * (k - 1)) by(nonlinear_arith)
            requires j >= k, k >= 1;
        assert(j * (j - 1) / 2 >= n) by(nonlinear_arith)
            requires j * (j - 1) >= 2 * n;
    }

    proof fn lemma_count_tail(n: int, lo: int, hi: int)
        requires
            lo >= 0,
            hi >= lo,
            n >= 1,
            forall |j: int| lo < j && j <= hi ==> !Self::is_valid_k(n, j),
        ensures
            Self::count_ways(n, hi) == Self::count_ways(n, lo),
        decreases hi - lo,
    {
        if hi > lo {
            Self::lemma_count_tail(n, lo, hi - 1);
        }
    }

    pub fn consecutive_numbers_sum(n: i32) -> (result: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result as int == Self::count_ways(n as int, n as int),
    {
        let n64: i64 = n as i64;
        let mut count: i32 = 0;
        let mut k: i64 = 1;
        let mut sum: i64 = 0;
        while sum < n64
            invariant
                1 <= k,
                k <= 100_000,
                k as int - 1 <= n as int,
                0 <= sum,
                n64 == n as i64,
                1 <= n64 <= 1_000_000_000,
                count >= 0,
                count as int <= k as int - 1,
                sum as int == k as int * (k as int - 1) / 2,
                count as int == Self::count_ways(n as int, k as int - 1),
            decreases 100_000 - k,
        {
            proof {
                assert(k as int * (k as int - 1) < 2 * n as int) by(nonlinear_arith)
                    requires sum < n64,
                             sum as int == k as int * (k as int - 1) / 2,
                             n64 == n as i64;
                Self::lemma_k_bound(k as int, n as int);
            }
            let r: i64 = (n64 - sum) % k;
            proof {
                assert(r as int == (n as int - k as int * (k as int - 1) / 2) % (k as int));
                if r == 0 {
                    assert(Self::is_valid_k(n as int, k as int));
                } else {
                    assert(!Self::is_valid_k(n as int, k as int));
                }
                assert((k as int + 1) * k as int / 2 == k as int * (k as int - 1) / 2 + k as int) by(nonlinear_arith);
            }
            if r == 0 {
                count = count + 1;
            }
            sum = sum + k;
            k = k + 1;
        }
        proof {
            assert(k as int * (k as int - 1) >= 2 * n as int) by(nonlinear_arith)
                requires sum as int == k as int * (k as int - 1) / 2,
                         sum as int >= n64 as int,
                         n64 == n as i64;
            assert forall |j: int| (k as int - 1) < j && j <= n as int implies !Self::is_valid_k(n as int, j) by {
                Self::lemma_invalid_above(n as int, k as int, j);
            }
            Self::lemma_count_tail(n as int, k as int - 1, n as int);
        }
        count
    }
}

} 