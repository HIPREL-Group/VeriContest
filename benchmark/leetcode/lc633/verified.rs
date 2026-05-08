use vstd::arithmetic::power::{lemma_square_is_pow2, pow};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn judge_square_sum_spec(c: int) -> bool {
        exists|a: nat, b: nat| pow(a as int, 2) + pow(b as int, 2) == c
    }

    pub fn judge_square_sum(c: i32) -> bool
        requires
            0 <= c,
        returns
            Self::judge_square_sum_spec(c as int),
    {
        let c64: i64 = c as i64;

        let mut lo: i64 = 0;
        let mut hi: i64 = if c64 <= 46340 { c64 } else { 46340 };
        while lo <= hi
            invariant
                0 <= c64 == c as i64,
                0 <= lo,
                lo <= hi + 1,
                0 <= hi,
                hi <= c64,
                hi <= 46340,
                (lo == 0) || ((lo - 1) * (lo - 1) <= c64),
                (hi >= c64) || ((hi + 1) * (hi + 1) > c64),
            decreases
                hi - lo + 1,
        {
            let mid: i64 = lo + (hi - lo) / 2;
            proof {
                assert(0 <= mid <= 46340);
                assert(mid * mid <= 46340i64 * 46340i64) by (nonlinear_arith)
                    requires 0 <= mid, mid <= 46340i64;
                assert(46340i64 * 46340i64 <= i64::MAX) by (nonlinear_arith);
            }
            let sq: i64 = mid * mid;
            if sq <= c64 {
                lo = mid + 1;
            } else {
                proof {
                    assert(mid >= 1) by (nonlinear_arith)
                        requires sq > c64, c64 >= 0, mid >= 0, sq == mid * mid;
                }
                hi = mid - 1;
            }
        }
        let right_init: i64 = hi;
        proof {
            assert(lo == hi + 1);
            assert(right_init == hi);
            assert(right_init >= 0);
            assert(right_init <= 46340);
            assert(lo >= 1);
            assert((lo - 1) * (lo - 1) <= c64);
            assert(right_init == lo - 1);
            assert(right_init * right_init <= c64);

            if hi >= c64 {
                assert((hi + 1) * (hi + 1) > c64) by (nonlinear_arith) requires hi >= c64, c64 >= 0;
            }
            assert((right_init + 1) * (right_init + 1) > c64);
        }

        let mut left: i64 = 0;
        let mut right: i64 = right_init;
        let ghost r0: int = right_init as int;

        proof {
            assert(r0 == right_init);
            assert(r0 * r0 <= c64);
            assert((r0 + 1) * (r0 + 1) > c64);
            assert(r0 <= 46340);
        }

        while left <= right
            invariant
                c64 == c as i64,
                0 <= left,
                0 <= right,
                right <= r0,
                r0 * r0 <= c64,
                r0 <= 46340,
                (r0 + 1) * (r0 + 1) > c64 as int,
                forall|a: int, b: int|
                    0 <= a < left && 0 <= b <= r0 ==> #[trigger] (a * a + b * b) != c64,
                forall|a: int, b: int|
                    0 <= a <= r0 && right < b <= r0 ==> #[trigger] (a * a + b * b) != c64,
            decreases
                right - left + 1,
        {
            proof {
                assert(left <= r0);
                assert(right <= r0);
                assert(0 <= left <= 46340);
                assert(0 <= right <= 46340);
                assert(left * left <= 46340i64 * 46340i64) by (nonlinear_arith)
                    requires 0 <= left, left <= 46340i64;
                assert(right * right <= 46340i64 * 46340i64) by (nonlinear_arith)
                    requires 0 <= right, right <= 46340i64;
                assert(46340i64 * 46340i64 <= i64::MAX) by (nonlinear_arith);
                assert(left * left + right * right <= 2 * 46340i64 * 46340i64) by (nonlinear_arith)
                    requires 0 <= left, left <= 46340i64, 0 <= right, right <= 46340i64;
                assert(2 * 46340i64 * 46340i64 <= i64::MAX) by (nonlinear_arith);
            }
            let sum: i64 = left * left + right * right;
            if sum == c64 {
                proof {
                    lemma_square_is_pow2(left as int);
                    lemma_square_is_pow2(right as int);
                    assert(pow(left as int, 2) + pow(right as int, 2) == c as int);
                    assert(Self::judge_square_sum_spec(c as int));
                }
                return true;
            }
            if sum < c64 {
                proof {
                    assert(left <= 46340);
                    assert forall|b: int| 0 <= b <= r0 implies #[trigger] (left * left + b * b) != c64 by {
                        if b <= right {
                            assert(b * b <= right * right) by (nonlinear_arith)
                                requires 0 <= b, b <= right;
                            assert(left * left + b * b <= left * left + right * right);
                            assert(left * left + right * right < c64);
                        } else {
                            assert(b > right);
                            assert(b * b >= (right + 1) * (right + 1)) by (nonlinear_arith)
                                requires b >= right + 1, right >= 0;
                            assert(left * left + b * b >= left * left + (right + 1) * (right + 1));
                        }
                    };
                }
                left += 1;
            } else {
                proof {
                    assert(left * left + right * right > c64);
                    assert forall|a: int| 0 <= a <= r0 implies #[trigger] (a * a + right * right) != c64 by {
                        if a >= left {
                            assert(a * a >= left * left) by (nonlinear_arith)
                                requires a >= left, left >= 0;
                            assert(a * a + right * right >= left * left + right * right);
                            assert(a * a + right * right > c64);
                        } else {
                            assert(0 <= a < left);
                        }
                    };
                    assert(right >= 1);
                }
                right -= 1;
            }
        }
        proof {
            assert(left > right);
            assert forall|a: nat, b: nat| pow(a as int, 2) + pow(b as int, 2) == c as int implies false by {
                lemma_square_is_pow2(a as int);
                lemma_square_is_pow2(b as int);
                assert((a as int) * (a as int) + (b as int) * (b as int) == c as int);
                assert((a as int) * (a as int) <= c64 as int);
                assert((b as int) * (b as int) <= c64 as int);
                assert(a as int <= r0) by (nonlinear_arith)
                    requires
                        (a as int) * (a as int) <= c64 as int,
                        (r0 + 1) * (r0 + 1) > c64 as int,
                        a >= 0nat,
                        r0 >= 0;
                assert(b as int <= r0) by (nonlinear_arith)
                    requires
                        (b as int) * (b as int) <= c64 as int,
                        (r0 + 1) * (r0 + 1) > c64 as int,
                        b >= 0nat,
                        r0 >= 0;
                if (a as int) < left {
                    assert(0 <= a as int);
                    assert((a as int) < left);
                    assert(0 <= b as int);
                    assert((b as int) <= r0);
                    assert(((a as int) * (a as int) + (b as int) * (b as int)) != c64 as int);
                } else {
                    assert((a as int) >= left);
                    assert((a as int) > right);
                    if (b as int) < left {
                        assert(0 <= b as int);
                        assert((b as int) < left);
                        assert(0 <= a as int);
                        assert((a as int) <= r0);
                        assert(((b as int) * (b as int) + (a as int) * (a as int)) != c64 as int);
                        assert(((a as int) * (a as int) + (b as int) * (b as int))
                            == ((b as int) * (b as int) + (a as int) * (a as int)));
                    } else {
                        assert((b as int) > right);
                        assert(0 <= a as int);
                        assert((a as int) <= r0);
                        assert(right < (b as int));
                        assert((b as int) <= r0);
                        assert(((a as int) * (a as int) + (b as int) * (b as int)) != c64 as int);
                    }
                }
            };
            assert(!Self::judge_square_sum_spec(c as int));
        }
        false
    }
}

}
