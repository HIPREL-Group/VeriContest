use vstd::arithmetic::power::{lemma_square_is_pow2, pow};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_is_perfect_square(num: int) -> bool {
        exists|k: nat| pow(k as int, 2) == num
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn is_perfect_square(num: i32) -> bool
        requires
            1 <= num <= i32::MAX,
        returns
            Self::spec_is_perfect_square(num as int),
    {
        let n: i64 = num as i64;
        let (mut l, mut r) = (1i64, n);

        
        proof {
            assert forall |k: nat| pow(k as int, 2) == n implies 1 <= k <= n by {
                lemma_square_is_pow2(k as int);
                assert(k >= 1 && k <= n) by (nonlinear_arith)
                    requires
                        pow(k as int, 2) == (k as int) * (k as int),
                        (k as int) * (k as int) == n,
                        n >= 1,
                ;
            }
        }

        while l <= r
            invariant
                n == num,
                1 <= n <= i32::MAX,
                1 <= l,
                r <= n,
                l <= r + 1,
                forall |k: nat| pow(k as int, 2) == n ==> l <= k <= r,
        {
            let mid: i64 = l + (r - l) / 2;

            assert(l <= mid && mid <= r) by (nonlinear_arith)
                requires l <= r, mid == l + (r - l) / 2;

            assert(mid <= i32::MAX) by (nonlinear_arith)
                requires mid <= r, r <= n, n <= i32::MAX;

            assert(mid * mid <= i64::MAX) by (nonlinear_arith)
                requires 0 <= mid <= i32::MAX;

            let sq: i64 = mid * mid;

            if sq == n {
                proof {
                    lemma_square_is_pow2(mid as int);
                    assert(Self::spec_is_perfect_square(n as int)) by {
                        assert(pow(mid as nat as int, 2) == n);
                    }
                }
                return true;
            } else if sq < n {
                proof {
                    assert forall |k: nat| pow(k as int, 2) == n implies mid + 1 <= k <= r by {
                        lemma_square_is_pow2(k as int);
                        assert(k > mid) by (nonlinear_arith)
                            requires
                                (k as int) * (k as int) == n,
                                mid * mid < n,
                                pow(k as int, 2) == (k as int) * (k as int),
                                l <= k <= r,
                                k >= 0,
                                mid >= 0,
                        ;
                    }
                }
                l = mid + 1;
            } else {
                proof {
                    assert forall |k: nat| pow(k as int, 2) == n implies l <= k <= mid - 1 by {
                        lemma_square_is_pow2(k as int);
                        assert(k < mid) by (nonlinear_arith)
                            requires
                                (k as int) * (k as int) == n,
                                mid * mid > n,
                                pow(k as int, 2) == (k as int) * (k as int),
                                l <= k,
                                k <= r,
                                k >= 0,
                                mid >= 1,
                        ;
                    }
                }
                r = mid - 1;
            }
        }

        proof {
            assert(!Self::spec_is_perfect_square(n as int)) by {
                assert forall |k: nat| pow(k as int, 2) == n implies false by {
                    assert(l > r);
                }
            }
        }
        false
    }
}

} 
