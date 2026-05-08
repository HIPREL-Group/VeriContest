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
        while num <= right {
            let mut tmp: i32 = num;
            let mut bits: i32 = 0;
            while tmp > 0 {
                let bit = tmp % 2;
                bits = bits + bit;
                tmp = tmp / 2;
            }
            let prime = Self::is_small_prime(bits);
            let add: i32 = if prime { 1 } else { 0 };
            result = result + add;
            num = num + 1;
        }
        result
    }
}

}
