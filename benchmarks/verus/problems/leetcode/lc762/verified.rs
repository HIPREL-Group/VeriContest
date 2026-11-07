use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn popcount_helper(x: int, acc: int) -> int
        decreases x,
    {
        if x <= 0 {
            acc
        } else {
            Self::popcount_helper(x / 2, acc + (x % 2))
        }
    }

    pub open spec fn popcount(x: int) -> int {
        Self::popcount_helper(x, 0)
    }

    pub open spec fn has_prime_set_bits(x: int) -> bool {
        let bits = Self::popcount(x);
        bits == 2 || bits == 3 || bits == 5 || bits == 7 || bits == 11 || bits == 13 || bits == 17 || bits == 19
    }

    pub open spec fn range_prime_count(left: int, right: int) -> int
        decreases if left <= right { right - left + 1 } else { 0 },
    {
        if left > right {
            0
        } else {
            Self::range_prime_count(left, right - 1)
                + if Self::has_prime_set_bits(right) { 1int } else { 0int }
        }
    }

    proof fn lemma_popcount_helper_additive(x: int, acc: int)
        requires
            x >= 0,
            acc >= 0,
        ensures
            Self::popcount_helper(x, acc) == Self::popcount(x) + acc,
            Self::popcount_helper(x, acc) >= acc,
        decreases x,
    {
        if x > 0 {
            Self::lemma_popcount_helper_additive(x / 2, acc + (x % 2));
            Self::lemma_popcount_helper_additive(x / 2, x % 2);
            assert(x % 2 >= 0);
        }
    }

    proof fn lemma_popcount_step(x: int)
        requires
            x >= 0,
        ensures
            Self::popcount(x) == Self::popcount(x / 2) + (x % 2),
    {
        Self::lemma_popcount_helper_additive(x / 2, x % 2);
    }

    proof fn lemma_popcount_nonneg(x: int)
        requires
            x >= 0,
        ensures
            Self::popcount(x) >= 0,
    {
        Self::lemma_popcount_helper_additive(x, 0);
    }

    proof fn lemma_popcount_le(x: int)
        requires
            x >= 0,
        ensures
            Self::popcount(x) <= x,
        decreases x,
    {
        if x > 0 {
            Self::lemma_popcount_le(x / 2);
            Self::lemma_popcount_step(x);
            assert(0 <= x % 2 <= 1);
            assert(x / 2 + (x % 2) <= x) by (nonlinear_arith)
                requires
                    x >= 0,
            {
            }
        }
    }

    pub fn is_small_prime(bits: i32) -> (res: bool)
        ensures
            res == (bits as int == 2 || bits as int == 3 || bits as int == 5 || bits as int == 7 || bits as int == 11 || bits as int == 13 || bits as int == 17 || bits as int == 19),
    {
        bits == 2 || bits == 3 || bits == 5 || bits == 7 || bits == 11 || bits == 13 || bits == 17 || bits == 19
    }

    pub fn count_prime_set_bits(left: i32, right: i32) -> (result: i32)
        requires
            1 <= left <= right <= 1_000_000,
            0 <= right - left <= 10_000,
        ensures
            result as int == Self::range_prime_count(left as int, right as int),
    {
        let mut result: i32 = 0;
        let mut num: i32 = left;
        while num <= right
            invariant
                1 <= left <= right <= 1_000_000,
                0 <= right - left <= 10_000,
                left <= num <= right + 1,
                0 <= result as int <= num as int - left as int,
                result as int == Self::range_prime_count(left as int, num as int - 1),
            decreases right - num + 1,
        {
            let mut tmp: i32 = num;
            let mut bits: i32 = 0;
            proof {
                Self::lemma_popcount_nonneg(num as int);
            }
            while tmp > 0
                invariant
                    1 <= num <= 1_000_000,
                    0 <= tmp <= num,
                    0 <= bits as int <= Self::popcount(num as int),
                    Self::popcount_helper(tmp as int, bits as int) == Self::popcount(num as int),
                decreases tmp,
            {
                let ghost old_tmp = tmp as int;
                let ghost old_bits = bits as int;
                let bit = tmp % 2;
                proof {
                    assert(Self::popcount_helper(old_tmp, old_bits) == Self::popcount_helper(old_tmp / 2, old_bits + (old_tmp % 2)));
                    Self::lemma_popcount_helper_additive(old_tmp / 2, old_bits + bit as int);
                    Self::lemma_popcount_le(num as int);
                    assert(0 <= bit <= 1);
                    assert(Self::popcount_helper(old_tmp / 2, old_bits + bit as int) == Self::popcount(num as int));
                    assert(old_bits + bit as int <= Self::popcount(num as int));
                }
                bits = bits + bit;
                tmp = tmp / 2;
                proof {
                    assert(tmp as int == old_tmp / 2);
                    assert(bits as int == old_bits + (old_tmp % 2));
                    assert(Self::popcount_helper(tmp as int, bits as int) == Self::popcount(num as int));
                    Self::lemma_popcount_helper_additive(tmp as int, bits as int);
                    assert(bits as int <= Self::popcount_helper(tmp as int, bits as int));
                }
            }
            proof {
                assert(tmp == 0);
                assert(Self::popcount_helper(0, bits as int) == bits as int);
                assert(bits as int == Self::popcount(num as int));
            }
            let prime = Self::is_small_prime(bits);
            let add: i32 = if prime { 1 } else { 0 };
            proof {
                assert(add == 0 || add == 1);
                assert(num as int - left as int <= right as int - left as int);
                assert(right as int - left as int <= 10_000);
                assert(result as int <= 10_000);
                assert(result as int + add as int <= 10_001);
                assert(prime == (bits as int == 2 || bits as int == 3 || bits as int == 5 || bits as int == 7 || bits as int == 11 || bits as int == 13 || bits as int == 17 || bits as int == 19));
                assert(Self::has_prime_set_bits(num as int) == (bits as int == 2 || bits as int == 3 || bits as int == 5 || bits as int == 7 || bits as int == 11 || bits as int == 13 || bits as int == 17 || bits as int == 19));
                assert(add as int == if Self::has_prime_set_bits(num as int) { 1int } else { 0int });
                assert(Self::range_prime_count(left as int, num as int)
                    == Self::range_prime_count(left as int, num as int - 1)
                        + if Self::has_prime_set_bits(num as int) { 1int } else { 0int });
                assert(result as int + add as int == Self::range_prime_count(left as int, num as int));
            }
            result = result + add;
            num = num + 1;
        }
        result
    }
}

}
