use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    pub open spec fn count_prefix(m: int, n: int, x: int, i: int) -> int
        decreases if i < 0 { 0nat } else { i as nat },
    {
        if i <= 0 || m <= 0 || n <= 0 || x < 0 {
            0
        } else {
            Self::count_prefix(m, n, x, i - 1) + Self::min2(n, x / i)
        }
    }

    pub open spec fn count_le(m: int, n: int, x: int) -> int
        recommends
            1 <= m <= 30000,
            1 <= n <= 30000,
            0 <= x <= m * n,
    {
        Self::count_prefix(m, n, x, m)
    }

    proof fn lemma_count_full_prefix(m: int, n: int, i: int)
        requires
            1 <= m <= 30000,
            1 <= n <= 30000,
            0 <= i <= m,
        ensures
            Self::count_prefix(m, n, m * n, i) == i * n,
        decreases i,
    {
        if i > 0 {
            Self::lemma_count_full_prefix(m, n, i - 1);
            
            
            
            

            
            
            
            
            
            
            
            
            
            assert(i >= 1);
            assert(i <= m);
            assert(n >= 1);
            
            
            assert(m / i >= 1) by (nonlinear_arith)
                requires i >= 1, i <= m, m >= 1;
            
            
            
            
            
            let mi = m / i;
            assert(mi >= 1);
            assert(mi * i <= m) by (nonlinear_arith)
                requires mi == m / i, i >= 1;
            assert(mi * i * n <= m * n) by (nonlinear_arith)
                requires mi * i <= m, n >= 1;
            assert(mi * n * i <= m * n) by (nonlinear_arith)
                requires mi * i * n <= m * n;
            
            assert(mi * n * i / i == mi * n) by (nonlinear_arith)
                requires i >= 1, mi >= 0, n >= 0;
            assert((m * n) / i >= mi * n) by (nonlinear_arith)
                requires
                    mi * n * i <= m * n,
                    i >= 1,
                    mi >= 0,
                    n >= 0,
            ;
            
            assert(mi * n >= n) by (nonlinear_arith)
                requires mi >= 1, n >= 1;
            assert((m * n) / i >= n);
            
            assert(Self::min2(n, (m * n) / i) == n);
            assert(Self::count_prefix(m, n, m * n, i - 1) == (i - 1) * n);
            assert(Self::count_prefix(m, n, m * n, i) == Self::count_prefix(m, n, m * n, i - 1) + Self::min2(n, (m * n) / i));
            assert(Self::count_prefix(m, n, m * n, i) == Self::count_prefix(m, n, m * n, i - 1) + n);
            assert(Self::count_prefix(m, n, m * n, i) == (i - 1) * n + n);
            assert((i - 1) * n + n == i * n) by (nonlinear_arith)
                requires
                    1 <= i,
                    1 <= n,
            ;
            assert(Self::count_prefix(m, n, m * n, i) == i * n);
        } else {
            assert(i == 0);
            assert(Self::count_prefix(m, n, m * n, i) == 0);
            assert(i * n == 0) by (nonlinear_arith)
                requires i == 0;
            assert(Self::count_prefix(m, n, m * n, i) == i * n);
        }
    }

    proof fn lemma_count_full(m: int, n: int)
        requires
            1 <= m <= 30000,
            1 <= n <= 30000,
        ensures
            Self::count_le(m, n, m * n) == m * n,
    {
        Self::lemma_count_full_prefix(m, n, m);
    }

    fn count_le_exec(m: i32, n: i32, x: i32) -> (cnt: i64)
        requires
            1 <= m <= 30000,
            1 <= n <= 30000,
            0 <= x,
            x as int <= m as int * n as int,
        ensures
            cnt as int == Self::count_le(m as int, n as int, x as int),
    {
        let mut i: i32 = 1;
        let mut cnt: i64 = 0;
        while i <= m
            invariant
                1 <= m <= 30000,
                1 <= n <= 30000,
                0 <= x,
                x as int <= m as int * n as int,
                1 <= i <= m + 1,
                0 <= cnt <= (i - 1) as i64 * n as i64,
                cnt as int == Self::count_prefix(m as int, n as int, x as int, (i - 1) as int),
            decreases m - i + 1,
        {
            let v = x / i;
            if v < n {
                assert(0 <= v);
                assert(v as i64 <= n as i64);
                assert(cnt <= (i - 1) as i64 * n as i64);
                assert(cnt + v as i64 <= i as i64 * n as i64) by (nonlinear_arith)
                    requires
                        cnt <= (i - 1) as i64 * n as i64,
                        v as i64 <= n as i64,
                ;
                assert(i as i64 * n as i64 <= 30000i64 * 30000i64) by (nonlinear_arith)
                    requires
                        i <= m,
                        m <= 30000,
                        1 <= n,
                        n <= 30000,
                ;
                cnt += v as i64;
                assert(Self::min2(n as int, (x / i) as int) == (x / i) as int);
            } else {
                assert(cnt <= (i - 1) as i64 * n as i64);
                assert(cnt + n as i64 <= i as i64 * n as i64) by (nonlinear_arith)
                    requires
                        cnt <= (i - 1) as i64 * n as i64,
                        1 <= n as i64,
                ;
                assert(i as i64 * n as i64 <= 30000i64 * 30000i64) by (nonlinear_arith)
                    requires
                        i <= m,
                        m <= 30000,
                        1 <= n,
                        n <= 30000,
                ;
                cnt += n as i64;
                assert(Self::min2(n as int, (x / i) as int) == n as int);
            }
            i += 1;
            assert(cnt as int == Self::count_prefix(m as int, n as int, x as int, (i - 1) as int));
        }
        cnt
    }

    pub fn find_kth_number(m: i32, n: i32, k: i32) -> (result: i32)
        requires
            1 <= m <= 30000,
            1 <= n <= 30000,
            1 <= k,
            k as int <= m as int * n as int,
        ensures
            1 <= result,
            result as int <= m as int * n as int,
            Self::count_le(m as int, n as int, result as int) >= k as int,
            result == 1 || Self::count_le(m as int, n as int, (result - 1) as int) < k as int,
    {
        assert(m as i64 * n as i64 <= 30000i64 * 30000i64) by (nonlinear_arith)
            requires
                1 <= m <= 30000i32,
                1 <= n <= 30000i32,
        ;

        let mut lo: i64 = 1;
        let mut hi: i64 = m as i64 * n as i64;

        proof {
            Self::lemma_count_full(m as int, n as int);
            assert(Self::count_le(m as int, n as int, hi as int) >= k as int);
        }

        while lo < hi
            invariant
                1 <= m <= 30000,
                1 <= n <= 30000,
                1 <= k,
                k as int <= m as int * n as int,
                1 <= lo <= hi,
                hi as int <= m as int * n as int,
                m as i64 * n as i64 <= 30000i64 * 30000i64,
                lo == 1 || Self::count_le(m as int, n as int, (lo - 1) as int) < k as int,
                Self::count_le(m as int, n as int, hi as int) >= k as int,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            assert(lo <= mid <= hi);
            assert(1 <= mid);
            assert(mid as int <= m as int * n as int);
            assert(mid <= i32::MAX as i64) by {
                assert(mid as int <= m as int * n as int);
                assert(m as i64 * n as i64 <= 30000i64 * 30000i64);
            }
            let cnt = Self::count_le_exec(m, n, mid as i32);
            assert(cnt as int == Self::count_le(m as int, n as int, mid as int));
            if cnt < k as i64 {
                assert(Self::count_le(m as int, n as int, mid as int) < k as int);
                lo = mid + 1;
            } else {
                assert(Self::count_le(m as int, n as int, mid as int) >= k as int);
                hi = mid;
            }
        }

        assert(lo == hi);
        assert(lo <= i32::MAX as i64) by {
            assert(lo as int <= m as int * n as int);
            assert(m as i64 * n as i64 <= 30000i64 * 30000i64);
        }
        lo as i32
    }
}

}
