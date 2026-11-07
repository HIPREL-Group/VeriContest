use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_div(x: int, d: int) -> int {
        (x + d - 1) / d
    }

    pub open spec fn stores_needed_prefix(quantities: Seq<i32>, x: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::stores_needed_prefix(quantities, x, n - 1)
                + Self::ceil_div(quantities[n - 1] as int, x)
        }
    }

    pub open spec fn stores_needed(quantities: Seq<i32>, x: int) -> int {
        Self::stores_needed_prefix(quantities, x, quantities.len() as int)
    }

    proof fn lemma_ceil_div_monotonic(x: int, d1: int, d2: int)
        requires
            1 <= x,
            1 <= d1 <= d2,
        ensures
            Self::ceil_div(x, d2) <= Self::ceil_div(x, d1),
    {
        assert((x + d2 - 1) * d1 <= (x + d1 - 1) * d2) by (nonlinear_arith)
            requires
                1 <= x,
                1 <= d1 <= d2,
        {
        }
        assert((x + d2 - 1) / d2 <= (x + d1 - 1) / d1) by (nonlinear_arith)
            requires
                1 <= d1,
                1 <= d2,
                (x + d2 - 1) * d1 <= (x + d1 - 1) * d2,
        {
        }
    }

    proof fn lemma_stores_needed_prefix_monotonic(quantities: Seq<i32>, d1: int, d2: int, n: int)
        requires
            0 <= n <= quantities.len(),
            1 <= d1 <= d2,
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
        ensures
            Self::stores_needed_prefix(quantities, d2, n) <= Self::stores_needed_prefix(quantities, d1, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_stores_needed_prefix_monotonic(quantities, d1, d2, n - 1);
            Self::lemma_ceil_div_monotonic(quantities[n - 1] as int, d1, d2);
        }
    }

    proof fn lemma_stores_needed_monotonic(quantities: Seq<i32>, d1: int, d2: int)
        requires
            1 <= d1 <= d2,
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
        ensures
            Self::stores_needed(quantities, d2) <= Self::stores_needed(quantities, d1),
    {
        Self::lemma_stores_needed_prefix_monotonic(quantities, d1, d2, quantities.len() as int);
    }

    proof fn lemma_stores_needed_at_100000(quantities: Seq<i32>, n: int)
        requires
            1 <= quantities.len() <= n,
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
        ensures
            Self::stores_needed(quantities, 100000) <= n,
    {
        assert forall |i: int| 0 <= i < quantities.len() implies Self::ceil_div(quantities[i] as int, 100000) == 1 by {
            assert(1 <= quantities[i] as int <= 100000);
            assert((quantities[i] as int + 100000 - 1) / 100000 == 1) by (nonlinear_arith)
                requires 1 <= quantities[i] as int <= 100000
            {
            }
        }
        Self::lemma_stores_needed_prefix_at_100000_equals_len(quantities, quantities.len() as int);
        assert(Self::stores_needed(quantities, 100000) == quantities.len() as int);
        assert(quantities.len() as int <= n);
    }

    proof fn lemma_stores_needed_prefix_at_100000_equals_len(quantities: Seq<i32>, n: int)
        requires
            0 <= n <= quantities.len(),
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
        ensures
            Self::stores_needed_prefix(quantities, 100000, n) == n,
        decreases n,
    {
        if n > 0 {
            Self::lemma_stores_needed_prefix_at_100000_equals_len(quantities, n - 1);
            assert(Self::ceil_div(quantities[n - 1] as int, 100000) == 1) by (nonlinear_arith)
                requires 1 <= quantities[n - 1] as int <= 100000
            {
            }
        }
    }

    fn stores_needed_exec(quantities: &Vec<i32>, x: i32) -> (need: i64)
        requires
            1 <= quantities.len() <= 100000,
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
            1 <= x <= 100000,
        ensures
            need as int == Self::stores_needed(quantities@, x as int),
            0 <= need as int <= quantities.len() as int * 100000,
    {
        let mut need: i64 = 0;
        let mut i: usize = 0;
        while i < quantities.len()
            invariant
                0 <= i <= quantities.len(),
                1 <= x <= 100000,
                1 <= quantities.len() <= 100000,
                forall |j: int| 0 <= j < quantities.len() ==> 1 <= #[trigger] quantities[j] <= 100000,
                need as int == Self::stores_needed_prefix(quantities@, x as int, i as int),
                0 <= need as int <= i as int * 100000,
            decreases quantities.len() - i,
        {
            let q = quantities[i];
            let add: i64 = (q as i64 + x as i64 - 1) / x as i64;
            proof {
                assert(add as int == Self::ceil_div(quantities[i as int] as int, x as int)) by (nonlinear_arith)
                    requires
                        q as int == quantities[i as int] as int,
                        1 <= x as int <= 100000,
                        add as int == (q as int + x as int - 1) / x as int,
                {
                }
                assert(1 <= add as int <= 100000) by (nonlinear_arith)
                    requires
                        1 <= quantities[i as int] as int <= 100000,
                        1 <= x as int,
                        add as int == (quantities[i as int] as int + x as int - 1) / x as int,
                {
                }
                assert(need as int + add as int <= (i as int + 1) * 100000) by (nonlinear_arith)
                    requires
                        0 <= need as int <= i as int * 100000,
                        1 <= add as int <= 100000,
                {
                }
            }
            need = need + add;
            i = i + 1;
        }
        need
    }

    pub fn minimized_maximum(n: i32, quantities: Vec<i32>) -> (ans: i32)
        requires
            1 <= quantities.len() <= n <= 100000,
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
        ensures
            1 <= ans <= 100000,
            Self::stores_needed(quantities@, ans as int) <= n as int,
            forall |x: int| 1 <= x < ans ==> #[trigger] Self::stores_needed(quantities@, x) > n as int,
    {
        proof {
            Self::lemma_stores_needed_at_100000(quantities@, n as int);
        }

        let mut left: i32 = 1;
        let mut right: i32 = 100000;
        while left < right
            invariant
                1 <= left <= right <= 100000,
                1 <= quantities.len() <= n <= 100000,
                Self::stores_needed(quantities@, right as int) <= n as int,
                forall |d: int| 1 <= d < left ==> #[trigger] Self::stores_needed(quantities@, d) > n as int,
                forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            let need = Self::stores_needed_exec(&quantities, mid);
            if need <= n as i64 {
                right = mid;
            } else {
                proof {
                    assert(Self::stores_needed(quantities@, mid as int) > n as int) by (nonlinear_arith)
                        requires
                            need as int == Self::stores_needed(quantities@, mid as int),
                            need > n as i64,
                    {
                    }
                    assert forall |d: int| 1 <= d < mid + 1 implies Self::stores_needed(quantities@, d) > n as int by {
                        if d < left {
                        } else {
                            assert(left <= d <= mid);
                            Self::lemma_stores_needed_monotonic(quantities@, d, mid as int);
                            assert(Self::stores_needed(quantities@, d) >= Self::stores_needed(quantities@, mid as int));
                        }
                    }
                }
                left = mid + 1;
            }
        }
        left
    }
}

}
