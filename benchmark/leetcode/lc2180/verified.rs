use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum_spec(n: nat) -> nat {
        (n / 1000) + ((n / 100) % 10) + ((n / 10) % 10) + (n % 10)
    }

    pub open spec fn is_even_digit_sum(n: nat) -> bool {
        Self::digit_sum_spec(n) % 2 == 0
    }

    pub open spec fn count_even_up_to(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::count_even_up_to((n - 1) as nat)
                + if Self::is_even_digit_sum(n) { 1nat } else { 0nat }
        }
    }

    proof fn lemma_count_even_up_to_le(n: nat)
        ensures
            Self::count_even_up_to(n) <= n,
        decreases n,
    {
        if n == 0 {
        } else {
            Self::lemma_count_even_up_to_le((n - 1) as nat);
            assert(Self::count_even_up_to(n)
                == Self::count_even_up_to((n - 1) as nat)
                    + if Self::is_even_digit_sum(n) { 1nat } else { 0nat });
        }
    }

    fn digit_sum(x: i32) -> (result: i32)
        requires
            1 <= x <= 1000,
        ensures
            result as nat == Self::digit_sum_spec(x as nat),
            0 <= result,
    {
        (x / 1000) + ((x / 100) % 10) + ((x / 10) % 10) + (x % 10)
    }

    fn even_contrib(x: i32) -> (result: i32)
        requires
            1 <= x <= 1000,
        ensures
            result as nat == if Self::is_even_digit_sum(x as nat) { 1nat } else { 0nat },
            0 <= result <= 1,
    {
        let s = Self::digit_sum(x);
        if s % 2 == 0 {
            1
        } else {
            0
        }
    }

    pub fn count_even(num: i32) -> (result: i32)
        requires
            1 <= num <= 1000,
        ensures
            result as nat == Self::count_even_up_to(num as nat),
            0 <= result <= num,
    {
        let mut i: i32 = 1;
        let mut count: i32 = 0;
        while i <= num
            invariant
                1 <= i <= num + 1,
                0 <= count,
                count as nat == Self::count_even_up_to((i - 1) as nat),
                1 <= num <= 1000,
            decreases num - i + 1,
        {
            let add = Self::even_contrib(i);
            proof {
                Self::lemma_count_even_up_to_le((i - 1) as nat);
            }
            assert(count <= 1000);
            assert(count + add <= 1001);
            count = count + add;
            assert(i <= 1000);
            assert(i + 1 <= 1001);
            i = i + 1;
            proof {
                assert(Self::count_even_up_to((i - 1) as nat)
                    == Self::count_even_up_to(((i - 1) as nat - 1) as nat)
                        + if Self::is_even_digit_sum((i - 1) as nat) { 1nat } else { 0nat });
            }
        }
        proof {
            Self::lemma_count_even_up_to_le(num as nat);
        }
        count
    }
}

}
