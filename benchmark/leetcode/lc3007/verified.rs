use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pow2_spec(exp: int) -> int
        decreases exp,
    {
        if exp <= 0 { 1 } else { 2 * Self::pow2_spec(exp - 1) }
    }

    pub open spec fn bit_price_upto(num: int, i: int) -> int {
        let n = num + 1;
        let block = Self::pow2_spec(i);
        let half = Self::pow2_spec(i - 1);
        let full = (n / block) * half;
        let rem = n % block;
        full + if rem > half { rem - half } else { 0 }
    }

    pub open spec fn total_price_upto(num: int, x: int, i: int) -> int
        decreases 61 - i,
    {
        if i > 60 {
            0
        } else {
            (if i % x == 0 { Self::bit_price_upto(num, i) } else { 0 })
                + Self::total_price_upto(num, x, i + 1)
        }
    }

    pub open spec fn count_price_upto_spec(num: int, x: int) -> int {
        if num < 0 { 0 } else { Self::total_price_upto(num, x, 1) }
    }

    pub open spec fn total_price_prefix(num: int, x: int, i: int) -> int
        decreases i,
    {
        if i <= 1 {
            0
        } else {
            Self::total_price_prefix(num, x, i - 1)
                + if (i - 1) % x == 0 { Self::bit_price_upto(num, i - 1) } else { 0 }
        }
    }

    pub proof fn lemma_total_prefix_suffix(num: int, x: int, i: int)
        requires
            1 <= i <= 61,
        ensures
            Self::total_price_prefix(num, x, i) + Self::total_price_upto(num, x, i)
                == Self::total_price_upto(num, x, 1),
        decreases i,
    {
        if i == 1 {
        } else {
            Self::lemma_total_prefix_suffix(num, x, i - 1);
        }
    }

    pub open spec fn find_maximum_number_spec(k: int, x: int, result: int) -> bool {
        &&& 1 <= k <= 1_000_000_000_000_000
        &&& 1 <= x <= 8
        &&& 0 <= result <= 1_152_921_504_606_846_975
        &&& Self::count_price_upto_spec(result, x) <= k
        &&& forall |candidate: int|
            0 <= candidate <= 1_152_921_504_606_846_975
                && Self::count_price_upto_spec(candidate, x) <= k
            ==> candidate <= result
    }

    pub proof fn lemma_pow2_spec_pos(exp: int)
        requires
            0 <= exp,
        ensures
            1 <= Self::pow2_spec(exp),
        decreases exp,
    {
        if exp == 0 {
        } else {
            Self::lemma_pow2_spec_pos(exp - 1);
        }
    }

    pub proof fn lemma_pow2_spec_bound_60(exp: int)
        requires
            0 <= exp <= 60,
        ensures
            Self::pow2_spec(exp) <= 1_152_921_504_606_846_976,
        decreases 60 - exp,
    {
        if exp < 60 {
            Self::lemma_pow2_spec_bound_60(exp + 1);
            Self::lemma_pow2_spec_pos(exp);
            assert(Self::pow2_spec(exp + 1) == 2 * Self::pow2_spec(exp));
            assert(Self::pow2_spec(exp) <= Self::pow2_spec(exp + 1)) by (nonlinear_arith)
                requires
                    1 <= Self::pow2_spec(exp),
                    Self::pow2_spec(exp + 1) == 2 * Self::pow2_spec(exp);
            assert(Self::pow2_spec(exp) <= 1_152_921_504_606_846_976) by (nonlinear_arith)
                requires
                    Self::pow2_spec(exp) <= Self::pow2_spec(exp + 1),
                    Self::pow2_spec(exp + 1) <= 1_152_921_504_606_846_976;
        } else {
            assert(Self::pow2_spec(60) == 1_152_921_504_606_846_976) by (compute);
        }
    }

    pub proof fn lemma_count_price_zero(x: int)
        requires
            1 <= x <= 8,
        ensures
            Self::count_price_upto_spec(0, x) == 0,
    {
        if x == 1 {
            assert(Self::count_price_upto_spec(0, 1) == 0) by (compute);
        } else if x == 2 {
            assert(Self::count_price_upto_spec(0, 2) == 0) by (compute);
        } else if x == 3 {
            assert(Self::count_price_upto_spec(0, 3) == 0) by (compute);
        } else if x == 4 {
            assert(Self::count_price_upto_spec(0, 4) == 0) by (compute);
        } else if x == 5 {
            assert(Self::count_price_upto_spec(0, 5) == 0) by (compute);
        } else if x == 6 {
            assert(Self::count_price_upto_spec(0, 6) == 0) by (compute);
        } else if x == 7 {
            assert(Self::count_price_upto_spec(0, 7) == 0) by (compute);
        } else {
            assert(x == 8);
            assert(Self::count_price_upto_spec(0, 8) == 0) by (compute);
        }
    }

    fn pow2(exp: i32) -> (result: i64)
        requires
            0 <= exp <= 60,
        ensures
            1 <= result,
            result as int == Self::pow2_spec(exp as int),
    {
        let mut p = 1i64;
        let mut t = 0i32;
        while t < exp
            invariant
                0 <= t <= exp <= 60,
                1 <= p,
                p as int == Self::pow2_spec(t as int),
                Self::pow2_spec(t as int) <= 1_152_921_504_606_846_976,
            decreases exp - t,
        {
            proof {
                Self::lemma_pow2_spec_bound_60(t as int + 1);
            }
            p = p.checked_mul(2).unwrap_or(i64::MAX);
            t += 1;
        }
        p
    }

    fn count_price_upto(num: i64, x: i32) -> (result: i64)
        requires
            0 <= num,
            0 <= num <= 1_152_921_504_606_846_975,
            1 <= x <= 8,
        ensures
            0 <= result,
            result < i64::MAX ==> result as int == Self::count_price_upto_spec(num as int, x as int),
            result == i64::MAX ==> Self::count_price_upto_spec(num as int, x as int) >= i64::MAX as int,
    {
        let n = if num == i64::MAX { i64::MAX } else { num + 1 };
        assert(num != i64::MAX);
        assert(n == num + 1);
        assert(n <= 1_152_921_504_606_846_976);
        let mut i = 1i32;
        let mut total = 0i64;
        while i <= 60
            invariant
                0 <= num <= 1_152_921_504_606_846_975,
                1 <= x <= 8,
                1 <= i <= 61,
                0 <= total,
                total <= i64::MAX,
                1 <= n,
                n == num + 1,
                total < i64::MAX ==> total as int == Self::total_price_prefix(num as int, x as int, i as int),
                total == i64::MAX ==> Self::total_price_prefix(num as int, x as int, i as int) >= i64::MAX as int,
            decreases 61 - i,
        {
            if i % x == 0 {
                let block = Self::pow2(i);
                let half = Self::pow2(i - 1);
                assert(block > 0);
                assert(block as int == Self::pow2_spec(i as int));
                assert(half as int == Self::pow2_spec(i as int - 1));
                assert(block as int == 2 * half as int);
                assert(0 < half <= block);
                assert(n <= 1_152_921_504_606_846_976);
                proof {
                    lemma_fundamental_div_mod(n as int, block as int);
                    assert(n == block * (n / block) + n % block);
                    assert((n / block) * block == block * (n / block)) by (nonlinear_arith);
                    assert((n / block) * block + n % block == n);
                    assert(0 <= n / block);
                    assert((n / block) * half <= (n / block) * block) by (nonlinear_arith)
                        requires
                            0 <= n / block,
                            half <= block;
                    assert((n / block) * block <= n) by (nonlinear_arith)
                        requires
                            (n / block) * block + n % block == n,
                            0 <= n % block;
                    assert((n / block) * half <= n) by (nonlinear_arith)
                        requires
                            (n / block) * half <= (n / block) * block,
                            (n / block) * block <= n;
                    assert((n / block) * half <= i64::MAX) by (nonlinear_arith)
                        requires
                            (n / block) * half <= n,
                            n <= 1_152_921_504_606_846_976;
                }
                let full = (n / block).checked_mul(half).unwrap_or(0);
                let rem = n % block;
                let extra = if rem > half { rem.checked_sub(half).unwrap_or(0) } else { 0 };
                assert(0 <= full);
                assert(0 <= extra);
                assert(full == (n / block) * half);
                assert(rem == n % block);
                if rem > half {
                    assert(extra == rem - half);
                    assert(full + extra <= (n / block) * block + rem) by (nonlinear_arith)
                        requires
                            full == (n / block) * half,
                            extra == rem - half,
                            block == 2 * half,
                            0 <= n / block,
                            0 <= half,
                            rem > half;
                    assert(full + extra <= n) by (nonlinear_arith)
                        requires
                            full + extra <= (n / block) * block + rem,
                            rem == n % block,
                            (n / block) * block + n % block == n;
                } else {
                    assert(extra == 0);
                    assert(full + extra <= n) by (nonlinear_arith)
                        requires
                            full == (n / block) * half,
                            extra == 0,
                            (n / block) * half <= n;
                }
                assert(full + extra <= i64::MAX) by (nonlinear_arith)
                    requires
                        full + extra <= n,
                        n <= 1_152_921_504_606_846_976;
                let add = full.checked_add(extra).unwrap_or(i64::MAX);
                assert(add >= 0);
                assert(add as int == Self::bit_price_upto(num as int, i as int)) by (nonlinear_arith)
                    requires
                        n == num + 1,
                        block as int == Self::pow2_spec(i as int),
                        half as int == Self::pow2_spec(i as int - 1),
                        full == (n / block) * half,
                        rem == n % block,
                        extra == if rem > half { rem - half } else { 0 },
                        add == full + extra;
                total = total.checked_add(add).unwrap_or(i64::MAX);
                assert(total < i64::MAX ==> total as int == Self::total_price_prefix(num as int, x as int, i as int + 1));
            } else {
                assert(Self::total_price_prefix(num as int, x as int, i as int + 1)
                    == Self::total_price_prefix(num as int, x as int, i as int));
            }
            i += 1;
        }
        proof {
            Self::lemma_total_prefix_suffix(num as int, x as int, 61);
            assert(Self::total_price_upto(num as int, x as int, 61) == 0);
            assert(Self::count_price_upto_spec(num as int, x as int)
                == Self::total_price_prefix(num as int, x as int, 61));
        }
        total
    }

    pub fn find_maximum_number(k: i64, x: i32) -> (result: i64)
        requires
            1 <= k <= 1_000_000_000_000_000,
            1 <= x <= 8,
        ensures
            Self::find_maximum_number_spec(k as int, x as int, result as int),
            0 <= result as int <= 1_152_921_504_606_846_975,
    {
        let upper = 1_152_921_504_606_846_975i64;
        let mut low = 0i64;
        let mut high = upper;
        let mut ans = 0i64;
        while low <= high
            invariant
                0 <= low <= upper + 1,
                -1 <= high <= upper,
                0 <= ans <= upper,
                upper == 1_152_921_504_606_846_975,
                1 <= k <= 1_000_000_000_000_000,
                1 <= x <= 8,
            decreases high - low + 1,
        {
            let mid = low + (high - low) / 2;
            assert(upper == 1_152_921_504_606_846_975);
            assert(0 <= low <= high <= upper);
            assert(0 <= high - low <= upper);
            assert(0 <= mid <= upper);
            assert(0 <= mid <= 1_152_921_504_606_846_975);
            let price = Self::count_price_upto(mid, x);
            if price <= k {
                ans = mid;
                if mid < upper {
                    low = mid + 1;
                } else {
                    break;
                }
            } else {
                high = mid - 1;
            }
        }
        ans = 0;
        proof {
            Self::lemma_count_price_zero(x as int);
        }
        let mut scan = 0i64;
        while scan <= upper
            invariant
                upper == 1_152_921_504_606_846_975,
                0 <= scan <= upper + 1,
                0 <= ans <= upper,
                1 <= k <= 1_000_000_000_000_000,
                1 <= x <= 8,
                Self::count_price_upto_spec(ans as int, x as int) <= k as int,
                forall |candidate: int|
                    0 <= candidate < scan
                        && Self::count_price_upto_spec(candidate, x as int) <= k as int
                    ==> candidate <= ans,
            decreases upper - scan + 1,
        {
            assert(0 <= scan <= 1_152_921_504_606_846_975);
            let price = Self::count_price_upto(scan, x);
            if price <= k {
                assert(price < i64::MAX);
                assert(Self::count_price_upto_spec(scan as int, x as int) <= k as int);
                ans = scan;
            } else {
                if price < i64::MAX {
                    assert(price as int == Self::count_price_upto_spec(scan as int, x as int));
                    assert(Self::count_price_upto_spec(scan as int, x as int) > k as int);
                } else {
                    assert(price == i64::MAX);
                    assert(Self::count_price_upto_spec(scan as int, x as int) >= i64::MAX as int);
                    assert(Self::count_price_upto_spec(scan as int, x as int) > k as int);
                }
            }
            assert forall |candidate: int|
                0 <= candidate < scan + 1
                    && Self::count_price_upto_spec(candidate, x as int) <= k as int
                implies candidate <= ans
            by {
                if candidate < scan {
                } else {
                    assert(candidate == scan);
                }
            }
            if scan < upper {
                scan += 1;
            } else {
                scan = upper + 1;
            }
        }
        assert(scan == upper + 1);
        ans
    }
}

}
