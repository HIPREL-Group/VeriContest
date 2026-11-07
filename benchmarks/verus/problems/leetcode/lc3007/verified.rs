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

    pub proof fn lemma_bit_price_upto_mono(num1: int, num2: int, i: int)
        requires
            0 <= num1 <= num2,
            1 <= i <= 60,
        ensures
            Self::bit_price_upto(num1, i) <= Self::bit_price_upto(num2, i),
    {
        let n1 = num1 + 1;
        let n2 = num2 + 1;
        let block = Self::pow2_spec(i);
        let half = Self::pow2_spec(i - 1);
        Self::lemma_pow2_spec_pos(i);
        Self::lemma_pow2_spec_pos(i - 1);
        assert(block == 2 * half);
        assert(0 < block);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(n1, n2, block);
        let q1 = n1 / block;
        let q2 = n2 / block;
        assert(q1 <= q2);
        let rem1 = n1 % block;
        let rem2 = n2 % block;
        lemma_fundamental_div_mod(n1, block);
        lemma_fundamental_div_mod(n2, block);
        assert(n1 == block * q1 + rem1);
        assert(n2 == block * q2 + rem2);
        assert(0 <= rem1 < block);
        assert(0 <= rem2 < block);
        assert(Self::bit_price_upto(num1, i) == q1 * half + (if rem1 > half { rem1 - half } else { 0 }));
        assert(Self::bit_price_upto(num2, i) == q2 * half + (if rem2 > half { rem2 - half } else { 0 }));
        if q1 < q2 {
            assert(q1 + 1 <= q2);
            assert(rem1 < 2 * half);
            assert(1 <= half);
            assert(Self::bit_price_upto(num1, i) < q1 * half + half) by (nonlinear_arith)
                requires
                    rem1 < 2 * half,
                    1 <= half,
                    Self::bit_price_upto(num1, i) == q1 * half + (if rem1 > half { rem1 - half } else { 0 }),
            {
            }
            assert(q1 * half + half <= q2 * half) by (nonlinear_arith)
                requires
                    q1 + 1 <= q2,
                    half >= 0,
            {
            }
            assert(q2 * half <= Self::bit_price_upto(num2, i)) by (nonlinear_arith)
                requires
                    Self::bit_price_upto(num2, i) == q2 * half + (if rem2 > half { rem2 - half } else { 0 }),
            {
            }
        } else {
            assert(q1 == q2);
            assert(rem1 <= rem2) by (nonlinear_arith)
                requires
                    n1 <= n2,
                    n1 == block * q1 + rem1,
                    n2 == block * q1 + rem2,
            {
            }
        }
    }

    proof fn lemma_total_price_upto_mono(num1: int, num2: int, x: int, i: int)
        requires
            0 <= num1 <= num2,
            1 <= x <= 8,
            1 <= i <= 61,
        ensures
            Self::total_price_upto(num1, x, i) <= Self::total_price_upto(num2, x, i),
        decreases 61 - i,
    {
        if i > 60 {
        } else {
            Self::lemma_total_price_upto_mono(num1, num2, x, i + 1);
            if i % x == 0 {
                Self::lemma_bit_price_upto_mono(num1, num2, i);
            }
        }
    }

    pub proof fn lemma_count_price_upto_spec_mono(num1: int, num2: int, x: int)
        requires
            0 <= num1 <= num2,
            1 <= x <= 8,
        ensures
            Self::count_price_upto_spec(num1, x) <= Self::count_price_upto_spec(num2, x),
    {
        Self::lemma_total_price_upto_mono(num1, num2, x, 1);
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
                low <= high + 1,
                low > 0 ==> ans as int == low as int - 1,
                low == 0 ==> ans == 0,
                low > 0 ==> Self::count_price_upto_spec(low as int - 1, x as int) <= k as int,
                high < upper ==> Self::count_price_upto_spec(high as int + 1, x as int) > k as int,
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
                assert(price < i64::MAX);
                assert(Self::count_price_upto_spec(mid as int, x as int) <= k as int);
                ans = mid;
                low = mid + 1;
            } else {
                if price < i64::MAX {
                    assert(price as int == Self::count_price_upto_spec(mid as int, x as int));
                } else {
                    assert(price == i64::MAX);
                    assert(Self::count_price_upto_spec(mid as int, x as int) >= i64::MAX as int);
                }
                assert(Self::count_price_upto_spec(mid as int, x as int) > k as int);
                high = mid - 1;
            }
        }
        assert(low == high + 1);
        if low > 0 {
            assert(Self::count_price_upto_spec(ans as int, x as int) <= k as int);
            if low <= upper {
                assert(high < upper);
                assert(Self::count_price_upto_spec(low as int, x as int) > k as int);
                assert forall |candidate: int|
                    0 <= candidate <= upper as int
                        && Self::count_price_upto_spec(candidate, x as int) <= k as int
                    implies candidate <= ans as int
                by {
                    if candidate >= low as int {
                        Self::lemma_count_price_upto_spec_mono(low as int, candidate, x as int);
                        assert(Self::count_price_upto_spec(candidate, x as int)
                            >= Self::count_price_upto_spec(low as int, x as int));
                        assert(false);
                    }
                }
            } else {
                assert(low == upper + 1);
                assert(ans == upper);
                assert forall |candidate: int|
                    0 <= candidate <= upper as int
                        && Self::count_price_upto_spec(candidate, x as int) <= k as int
                    implies candidate <= ans as int
                by {
                }
            }
        } else {
            assert(high == -1);
            assert(-1 < upper);
            assert(Self::count_price_upto_spec(0, x as int) > k as int);
            proof {
                Self::lemma_count_price_zero(x as int);
            }
            assert(false);
        }
        ans
    }
}

}
