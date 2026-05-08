use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pieces_prefix(candies: Seq<i32>, x: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::pieces_prefix(candies, x, n - 1) + (candies[n - 1] as int) / x
        }
    }

    pub open spec fn alloc_possible(candies: Seq<i32>, x: int, k: int) -> bool {
        if x <= 0 {
            true
        } else {
            Self::pieces_prefix(candies, x, candies.len() as int) >= k
        }
    }

    pub open spec fn max_elem_prefix(candies: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            candies[0] as int
        } else {
            let p = Self::max_elem_prefix(candies, n - 1);
            let c = candies[n - 1] as int;
            if p >= c { p } else { c }
        }
    }

    pub open spec fn max_elem(candies: Seq<i32>) -> int {
        Self::max_elem_prefix(candies, candies.len() as int)
    }

    proof fn lemma_div_monotonic_nonneg(a: int, x1: int, x2: int)
        requires
            0 <= a,
            1 <= x1 <= x2,
        ensures
            a / x2 <= a / x1,
    {
        assert((a / x2) * x2 <= a) by (nonlinear_arith)
            requires 1 <= x2
        {
        }
        assert((a / x2) * x1 <= (a / x2) * x2) by (nonlinear_arith)
            requires 0 <= a / x2, 1 <= x1 <= x2
        {
        }
        assert((a / x2) * x1 <= a) by (nonlinear_arith)
            requires (a / x2) * x1 <= (a / x2) * x2, (a / x2) * x2 <= a
        {
        }
        assert(a / x2 <= a / x1) by (nonlinear_arith)
            requires
                1 <= x1,
                (a / x2) * x1 <= a,
        {
        }
    }

    proof fn lemma_pieces_prefix_monotonic(candies: Seq<i32>, x1: int, x2: int, n: int)
        requires
            0 <= n <= candies.len(),
            1 <= x1 <= x2,
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
        ensures
            Self::pieces_prefix(candies, x2, n) <= Self::pieces_prefix(candies, x1, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_pieces_prefix_monotonic(candies, x1, x2, n - 1);
            Self::lemma_div_monotonic_nonneg(candies[n - 1] as int, x1, x2);
        }
    }

    proof fn lemma_pieces_prefix_len_monotonic(candies: Seq<i32>, x: int, n: int, m: int)
        requires
            1 <= x,
            0 <= n <= m <= candies.len(),
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
        ensures
            Self::pieces_prefix(candies, x, n) <= Self::pieces_prefix(candies, x, m),
        decreases m,
    {
        if m > n {
            Self::lemma_pieces_prefix_len_monotonic(candies, x, n, m - 1);
            assert(0 <= (candies[m - 1] as int) / x) by (nonlinear_arith)
                requires 0 <= candies[m - 1] as int, 1 <= x
            {
            }
            assert(Self::pieces_prefix(candies, x, m)
                == Self::pieces_prefix(candies, x, m - 1) + (candies[m - 1] as int) / x);
            assert(Self::pieces_prefix(candies, x, m - 1) <= Self::pieces_prefix(candies, x, m));
        }
    }

    proof fn lemma_alloc_monotonic(candies: Seq<i32>, x1: int, x2: int, k: int)
        requires
            1 <= x1 <= x2,
            1 <= k,
            Self::alloc_possible(candies, x2, k),
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
        ensures
            Self::alloc_possible(candies, x1, k),
    {
        Self::lemma_pieces_prefix_monotonic(candies, x1, x2, candies.len() as int);
    }

    proof fn lemma_max_elem_prefix_upper(candies: Seq<i32>, n: int, i: int)
        requires
            1 <= n <= candies.len(),
            0 <= i < n,
        ensures
            candies[i] as int <= Self::max_elem_prefix(candies, n),
        decreases n,
    {
        if n > 1 {
            if i < n - 1 {
                Self::lemma_max_elem_prefix_upper(candies, n - 1, i);
            }
        }
    }

    proof fn lemma_no_piece_when_gt_max(candies: Seq<i32>, x: int, n: int)
        requires
            0 <= n <= candies.len(),
            1 <= candies.len(),
            x > Self::max_elem(candies),
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
        ensures
            Self::pieces_prefix(candies, x, n) == 0,
        decreases n,
    {
        if n > 0 {
            Self::lemma_no_piece_when_gt_max(candies, x, n - 1);
            Self::lemma_max_elem_prefix_upper(candies, candies.len() as int, n - 1);
            assert((candies[n - 1] as int) < x);
            assert((candies[n - 1] as int) / x == 0) by (nonlinear_arith)
                requires 0 <= candies[n - 1] as int, (candies[n - 1] as int) < x, 1 <= x
            {
            }
        }
    }

    fn can_allocate(candies: &Vec<i32>, x: i32, k: i64) -> (ok: bool)
        requires
            1 <= candies.len() <= 100000,
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
            1 <= x <= 10000000,
            1 <= k <= 1000000000000,
        ensures
            ok == (Self::pieces_prefix(candies@, x as int, candies.len() as int) >= k as int),
    {
        let mut cnt: i64 = 0;
        let mut i: usize = 0;
        while i < candies.len()
            invariant
                0 <= i <= candies.len(),
                1 <= x <= 10000000,
                1 <= k <= 1000000000000,
                1 <= candies.len() <= 100000,
                forall |j: int| 0 <= j < candies.len() ==> 1 <= #[trigger] candies[j] <= 10000000,
                cnt as int == Self::pieces_prefix(candies@, x as int, i as int),
                0 <= cnt as int,
                cnt < k,
            decreases candies.len() - i,
        {
            let add = (candies[i] as i64) / (x as i64);
            if cnt >= k - add {
                proof {
                    assert(cnt as int + add as int == Self::pieces_prefix(candies@, x as int, (i + 1) as int));
                    assert(cnt as int + add as int >= k as int) by (nonlinear_arith)
                        requires cnt >= k - add
                    {
                    }
                    Self::lemma_pieces_prefix_len_monotonic(candies@, x as int, (i + 1) as int, candies.len() as int);
                    assert(Self::pieces_prefix(candies@, x as int, candies.len() as int) >= k as int);
                }
                return true;
            }
            cnt = cnt + add;
            i = i + 1;
        }
        false
    }

    pub fn maximum_candies(candies: Vec<i32>, k: i64) -> (ans: i32)
        requires
            1 <= candies.len() <= 100000,
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
            1 <= k <= 1000000000000,
        ensures
            0 <= ans <= Self::max_elem(candies@),
            Self::alloc_possible(candies@, ans as int, k as int),
            forall |x: int| ans < x <= Self::max_elem(candies@) ==> !#[trigger] Self::alloc_possible(candies@, x, k as int),
    {
        let mut max_v: i32 = candies[0];
        let mut i: usize = 1;
        while i < candies.len()
            invariant
                1 <= i <= candies.len(),
                1 <= candies.len() <= 100000,
                1 <= max_v <= 10000000,
                max_v as int == Self::max_elem_prefix(candies@, i as int),
                forall |j: int| 0 <= j < candies.len() ==> 1 <= #[trigger] candies[j] <= 10000000,
            decreases candies.len() - i,
        {
            if candies[i] > max_v {
                max_v = candies[i];
            }
            i = i + 1;
        }

        let mut lo: i32 = 0;
        let mut hi: i32 = max_v;
        while lo < hi
            invariant
                0 <= lo <= hi <= max_v <= 10000000,
                1 <= candies.len() <= 100000,
                1 <= k <= 1000000000000,
                max_v as int == Self::max_elem(candies@),
                Self::alloc_possible(candies@, lo as int, k as int),
                forall |x: int| hi < x <= max_v as int ==> !#[trigger] Self::alloc_possible(candies@, x, k as int),
                forall |j: int| 0 <= j < candies.len() ==> 1 <= #[trigger] candies[j] <= 10000000,
            decreases hi - lo,
        {
            let mid: i32 = lo + (hi - lo + 1) / 2;
            if Self::can_allocate(&candies, mid, k) {
                lo = mid;
            } else {
                proof {
                    assert(!Self::alloc_possible(candies@, mid as int, k as int));
                    assert forall |x: int| mid as int - 1 < x <= max_v as int implies !Self::alloc_possible(candies@, x, k as int) by {
                        if x > hi {
                        } else {
                            assert(x >= mid as int);
                            if Self::alloc_possible(candies@, x, k as int) {
                                Self::lemma_alloc_monotonic(candies@, mid as int, x, k as int);
                                assert(Self::alloc_possible(candies@, mid as int, k as int));
                            }
                        }
                    }
                }
                hi = mid - 1;
            }
        }

        lo
    }
}

}
