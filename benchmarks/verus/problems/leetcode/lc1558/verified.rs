use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    pub open spec fn popcount(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 } else { (n % 2) + Self::popcount(n / 2) }
    }

    
    
    pub open spec fn bit_length(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 } else { 1 + Self::bit_length(n / 2) }
    }

    pub open spec fn sum_popcount(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 } else { Self::sum_popcount(s, end - 1) + Self::popcount(s[end - 1] as int) }
    }

    pub open spec fn max_bit_length(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            let prev = Self::max_bit_length(s, end - 1);
            let curr = Self::bit_length(s[end - 1] as int);
            if curr > prev { curr } else { prev }
        }
    }

    pub open spec fn pow2_spec(k: nat) -> nat
        decreases k,
    {
        if k == 0 { 1 } else { 2 * Self::pow2_spec((k - 1) as nat) }
    }

    proof fn popcount_nonneg(n: int)
        requires
            n >= 0,
        ensures
            Self::popcount(n) >= 0,
        decreases n,
    {
        if n > 0 {
            Self::popcount_nonneg(n / 2);
        }
    }

    proof fn bit_length_nonneg(n: int)
        requires
            n >= 0,
        ensures
            Self::bit_length(n) >= 0,
        decreases n,
    {
        if n > 0 {
            Self::bit_length_nonneg(n / 2);
        }
    }

    proof fn popcount_le_bit_length(n: int)
        requires
            n >= 0,
        ensures
            Self::popcount(n) <= Self::bit_length(n),
        decreases n,
    {
        if n > 0 {
            Self::popcount_le_bit_length(n / 2);
        }
    }

    proof fn bit_length_lt_pow2(n: int, k: nat)
        requires
            0 <= n,
            n < Self::pow2_spec(k) as int,
        ensures
            Self::bit_length(n) <= k as int,
        decreases n,
    {
        if n > 0 {
            Self::bit_length_lt_pow2(n / 2, (k - 1) as nat);
        }
    }

    proof fn bit_length_le_30(n: int)
        requires
            0 <= n <= 1_000_000_000,
        ensures
            Self::bit_length(n) <= 30,
    {
        assert(Self::pow2_spec(30) == 1_073_741_824nat) by {
            reveal_with_fuel(Solution::pow2_spec, 32);
        };
        Self::bit_length_lt_pow2(n, 30);
    }

    proof fn sum_popcount_bound(s: Seq<i32>, end: int)
        requires
            end >= 0,
            end <= s.len(),
            forall |j: int| 0 <= j < end ==> 0 <= #[trigger] s[j] <= 1_000_000_000,
        ensures
            Self::sum_popcount(s, end) <= 30 * end,
        decreases end,
    {
        if end > 0 {
            Self::sum_popcount_bound(s, end - 1);
            Self::popcount_le_bit_length(s[end - 1] as int);
            Self::bit_length_le_30(s[end - 1] as int);
        }
    }

    proof fn sum_popcount_nonneg(s: Seq<i32>, end: int)
        requires
            end >= 0,
            end <= s.len(),
            forall |j: int| 0 <= j < end ==> #[trigger] s[j] >= 0,
        ensures
            Self::sum_popcount(s, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::sum_popcount_nonneg(s, end - 1);
            Self::popcount_nonneg(s[end - 1] as int);
        }
    }

    proof fn max_bit_length_nonneg(s: Seq<i32>, end: int)
        requires
            end >= 0,
            end <= s.len(),
            forall |j: int| 0 <= j < end ==> #[trigger] s[j] >= 0,
        ensures
            Self::max_bit_length(s, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::max_bit_length_nonneg(s, end - 1);
            Self::bit_length_nonneg(s[end - 1] as int);
        }
    }

    proof fn max_bit_length_bound(s: Seq<i32>, end: int)
        requires
            end >= 0,
            end <= s.len(),
            forall |j: int| 0 <= j < end ==> 0 <= #[trigger] s[j] <= 1_000_000_000,
        ensures
            Self::max_bit_length(s, end) <= 30,
        decreases end,
    {
        if end > 0 {
            Self::max_bit_length_bound(s, end - 1);
            Self::bit_length_le_30(s[end - 1] as int);
        }
    }

    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    pub fn min_operations(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums@.len() <= 100_000,
            forall |i: int| 0 <= i < nums@.len() ==> 0 <= #[trigger] nums@[i] <= 1_000_000_000,
        ensures
            result as int == Self::sum_popcount(nums@, nums@.len() as int) +
                if Self::max_bit_length(nums@, nums@.len() as int) > 0 {
                    Self::max_bit_length(nums@, nums@.len() as int) - 1
                } else {
                    0int
                },
    {
        let mut ones: i32 = 0;
        let mut max_len: i32 = 0;
        let n = nums.len();
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == nums@.len(),
                1 <= n <= 100_000,
                forall |j: int| 0 <= j < n ==> 0 <= #[trigger] nums@[j] <= 1_000_000_000,
                ones as int == Self::sum_popcount(nums@, i as int),
                max_len as int == Self::max_bit_length(nums@, i as int),
                0 <= ones <= 30 * i as int,
                0 <= max_len <= 30,
            decreases n - i,
        {
            let mut val = nums[i];
            let mut bits: i32 = 0;
            let mut len: i32 = 0;

            proof {
                Self::bit_length_le_30(nums@[i as int] as int);
                Self::popcount_le_bit_length(nums@[i as int] as int);
                Self::popcount_nonneg(nums@[i as int] as int);
                Self::bit_length_nonneg(nums@[i as int] as int);
            }

            while val > 0
                invariant
                    0 <= i < n,
                    n == nums@.len(),
                    val >= 0,
                    bits >= 0,
                    len >= 0,
                    bits as int + Self::popcount(val as int) == Self::popcount(nums@[i as int] as int),
                    len as int + Self::bit_length(val as int) == Self::bit_length(nums@[i as int] as int),
                    bits as int <= len as int,
                    Self::bit_length(nums@[i as int] as int) <= 30,
                    Self::popcount(nums@[i as int] as int) <= Self::bit_length(nums@[i as int] as int),
                decreases val,
            {
                proof {
                    Self::popcount_nonneg(val as int / 2);
                    Self::bit_length_nonneg(val as int / 2);
                }
                if val % 2 == 1 {
                    bits = bits + 1;
                }
                val = val / 2;
                len = len + 1;
            }

            ones = ones + bits;
            if len > max_len {
                max_len = len;
            }
            i = i + 1;
        }

        if max_len > 0 {
            ones + max_len - 1
        } else {
            ones
        }
    }
}

}
