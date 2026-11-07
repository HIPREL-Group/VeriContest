use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn all_lucky_digits(digits: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < digits.len() ==> (#[trigger] digits[i] == 4u8 || digits[i] == 7u8)
}

pub open spec fn sum_range(digits: Seq<u8>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0int
    } else {
        digits[lo] as int + sum_range(digits, lo + 1, hi)
    }
}

pub open spec fn all_lucky_prefix(digits: Seq<u8>, k: int) -> bool {
    forall|i: int| 0 <= i < k ==> (#[trigger] digits[i] == 4u8 || digits[i] == 7u8)
}

pub open spec fn sum_prefix(digits: Seq<u8>, lo: int, k: int) -> int
    decreases k - lo,
{
    if k <= lo {
        0int
    } else {
        sum_prefix(digits, lo, k - 1) + digits[k - 1] as int
    }
}

proof fn lemma_sum_prefix_eq_range(digits: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= digits.len(),
    ensures
        sum_prefix(digits, lo, hi) == sum_range(digits, lo, hi),
    decreases hi - lo,
{
    if hi <= lo {
    } else {
        lemma_sum_prefix_eq_range(digits, lo, hi - 1);
        lemma_sum_range_split(digits, lo, hi - 1, hi);
        assert(sum_range(digits, hi - 1, hi) == digits[hi - 1] as int) by {
            assert(sum_range(digits, hi, hi) == 0int);
        }
    }
}

proof fn lemma_sum_range_split(digits: Seq<u8>, lo: int, mid: int, hi: int)
    requires
        0 <= lo <= mid <= hi <= digits.len(),
    ensures
        sum_range(digits, lo, hi) == sum_range(digits, lo, mid) + sum_range(digits, mid, hi),
    decreases mid - lo,
{
    if lo >= mid {
    } else {
        lemma_sum_range_split(digits, lo + 1, mid, hi);
    }
}

impl Solution {
    pub fn is_lucky_ticket(n: usize, digits: Vec<u8>) -> (res: bool)
        requires
            2 <= n <= 50,
            n % 2 == 0,
            digits.len() == n,
            forall|i: int| 0 <= i < digits.len() ==> #[trigger] digits[i] <= 9u8,
        ensures
            res == (all_lucky_digits(digits@) && sum_range(digits@, 0, (n / 2) as int) == sum_range(digits@, (n / 2) as int, n as int)),
    {
        let mut all_lucky = true;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                digits.len() == n,
                all_lucky == all_lucky_prefix(digits@, i as int),
            decreases n - i,
        {
            if digits[i] != 4u8 && digits[i] != 7u8 {
                all_lucky = false;
            }
            i += 1;
        }
        assert(all_lucky == all_lucky_digits(digits@));
        if !all_lucky {
            return false;
        }
        let half = n / 2;
        let mut sum1: u64 = 0;
        let mut sum2: u64 = 0;
        let mut j: usize = 0;
        while j < half
            invariant
                0 <= j <= half,
                half == n / 2,
                digits.len() == n,
                2 <= n <= 50,
                forall|i: int| 0 <= i < digits.len() ==> #[trigger] digits[i] <= 9u8,
                sum1 as int == sum_prefix(digits@, 0, j as int),
                sum1 as int <= 9 * j as int,
            decreases half - j,
        {
            sum1 = sum1 + digits[j] as u64;
            j += 1;
        }
        proof {
            lemma_sum_prefix_eq_range(digits@, 0, half as int);
        }
        let mut k: usize = half;
        while k < n
            invariant
                half <= k <= n,
                half == n / 2,
                digits.len() == n,
                2 <= n <= 50,
                forall|i: int| 0 <= i < digits.len() ==> #[trigger] digits[i] <= 9u8,
                sum2 as int == sum_prefix(digits@, half as int, k as int),
                sum2 as int <= 9 * (k - half) as int,
            decreases n - k,
        {
            sum2 = sum2 + digits[k] as u64;
            k += 1;
        }
        proof {
            lemma_sum_prefix_eq_range(digits@, half as int, n as int);
        }
        sum1 == sum2
    }
}

}
