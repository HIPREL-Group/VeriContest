use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn paint_ways(n: int, k: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else if n == 1 {
            k
        } else if n == 2 {
            k * k
        } else {
            (k - 1) * (Self::paint_ways(n - 1, k) + Self::paint_ways(n - 2, k))
        }
    }

    proof fn paint_ways_nonnegative(n: int, k: int)
        requires
            0 <= n,
            1 <= k,
        ensures
            0 <= Self::paint_ways(n, k),
        decreases n,
    {
        if n <= 2 {
        } else {
            Self::paint_ways_nonnegative(n - 1, k);
            Self::paint_ways_nonnegative(n - 2, k);
        }
    }

    proof fn paint_ways_step_monotonic(n: int, k: int)
        requires
            0 <= n,
            2 <= k,
        ensures
            Self::paint_ways(n, k) <= Self::paint_ways(n + 1, k),
    {
        if n == 0 {
        } else if n == 1 {
            assert(k <= k * k) by (nonlinear_arith)
                requires
                    2 <= k,
            {}
        } else {
            Self::paint_ways_nonnegative(n, k);
            Self::paint_ways_nonnegative(n - 1, k);
            assert((k - 1) * (Self::paint_ways(n, k) + Self::paint_ways(n - 1, k)) >= Self::paint_ways(n, k)) by (nonlinear_arith)
                requires
                    2 <= k,
                    0 <= Self::paint_ways(n, k),
                    0 <= Self::paint_ways(n - 1, k),
            {}
        }
    }

    proof fn paint_ways_monotonic(i: int, j: int, k: int)
        requires
            0 <= i <= j,
            2 <= k,
        ensures
            Self::paint_ways(i, k) <= Self::paint_ways(j, k),
        decreases j - i,
    {
        if i < j {
            Self::paint_ways_monotonic(i, j - 1, k);
            Self::paint_ways_step_monotonic(j - 1, k);
        }
    }

    proof fn paint_ways_k_one_le_one(n: int)
        requires
            1 <= n,
        ensures
            Self::paint_ways(n, 1) <= 1,
        decreases n,
    {
        if n <= 2 {
        } else {
            assert(Self::paint_ways(n, 1) == 0);
        }
    }

    pub fn num_ways(n: i32, k: i32) -> (res: i32)
        requires
            0 <= n <= 50,
            1 <= k <= 100000,
            Self::paint_ways(n as int, k as int) <= i32::MAX as int,
        ensures
            res as int == Self::paint_ways(n as int, k as int),
    {
        if n == 0 {
            return 0;
        }
        if n == 1 {
            return k;
        }

        proof {
            if k == 1 {
                assert((k as int) * (k as int) <= i32::MAX as int) by (nonlinear_arith)
                    requires
                        k == 1,
                {}
            } else {
                assert(2 <= k);
                if n > 2 {
                    Self::paint_ways_monotonic(2, n as int, k as int);
                }
                assert(Self::paint_ways(2, k as int) <= Self::paint_ways(n as int, k as int));
                assert(Self::paint_ways(2, k as int) == (k as int) * (k as int));
                assert((k as int) * (k as int) <= i32::MAX as int);
            }
        }
        let mut prev2: i32 = k;
        let mut prev1: i32 = k * k;
        let mut i: i32 = 3;
        while i <= n
            invariant
                2 <= n <= 50,
                1 <= k <= 100000,
                3 <= i <= n + 1,
                prev2 as int == Self::paint_ways((i - 2) as int, k as int),
                prev1 as int == Self::paint_ways((i - 1) as int, k as int),
                0 <= prev2 as int <= i32::MAX as int,
                0 <= prev1 as int <= i32::MAX as int,
                Self::paint_ways(n as int, k as int) <= i32::MAX as int,
            decreases n - i + 1,
        {
            proof {
                if k == 1 {
                    assert(i >= 3);
                    Self::paint_ways_nonnegative((i - 1) as int, 1);
                    Self::paint_ways_nonnegative((i - 2) as int, 1);
                    Self::paint_ways_k_one_le_one((i - 1) as int);
                    Self::paint_ways_k_one_le_one((i - 2) as int);
                    assert(prev1 as int + prev2 as int <= 2) by (nonlinear_arith)
                        requires
                            0 <= prev1 as int <= 1,
                            0 <= prev2 as int <= 1,
                    {}
                    assert(prev1 as int + prev2 as int <= i32::MAX as int);
                } else {
                    assert(2 <= k);
                    Self::paint_ways_nonnegative((i - 1) as int, k as int);
                    Self::paint_ways_nonnegative((i - 2) as int, k as int);
                    assert(Self::paint_ways(i as int, k as int) == (k as int - 1) * (Self::paint_ways((i - 1) as int, k as int) + Self::paint_ways((i - 2) as int, k as int)));
                    assert(Self::paint_ways(i as int, k as int) >= Self::paint_ways((i - 1) as int, k as int) + Self::paint_ways((i - 2) as int, k as int)) by (nonlinear_arith)
                        requires
                            2 <= k,
                            0 <= Self::paint_ways((i - 1) as int, k as int),
                            0 <= Self::paint_ways((i - 2) as int, k as int),
                    {}
                    assert(prev1 as int + prev2 as int <= Self::paint_ways(i as int, k as int));
                    Self::paint_ways_monotonic(i as int, n as int, k as int);
                    assert(Self::paint_ways(i as int, k as int) <= Self::paint_ways(n as int, k as int));
                    assert(prev1 as int + prev2 as int <= i32::MAX as int);
                }
            }
            let sum = prev1 + prev2;
            proof {
                assert(sum as int == prev1 as int + prev2 as int);
                if k == 1 {
                    assert(k - 1 == 0);
                    assert(0 <= (k as int - 1) * (sum as int) <= i32::MAX as int) by (nonlinear_arith)
                        requires
                            k == 1,
                    {}
                } else {
                    assert(2 <= k);
                    assert(Self::paint_ways(i as int, k as int) == (k as int - 1) * (sum as int));
                    Self::paint_ways_monotonic(i as int, n as int, k as int);
                    assert(Self::paint_ways(i as int, k as int) <= Self::paint_ways(n as int, k as int));
                    assert((k as int - 1) * (sum as int) <= i32::MAX as int);
                    assert(0 <= (k as int - 1) * (sum as int));
                }
            }
            let next = (k - 1) * sum;
            proof {
                assert(next as int == (k as int - 1) * (sum as int));
                assert(next as int == Self::paint_ways(i as int, k as int));
            }
            prev2 = prev1;
            prev1 = next;
            i = i + 1;
        }
        prev1
    }
}

}
