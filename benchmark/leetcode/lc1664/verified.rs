use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_even(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else if start % 2 == 0 {
        s[start] as int + sum_even(s, start + 1, end)
    } else {
        sum_even(s, start + 1, end)
    }
}

pub open spec fn sum_odd(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else if start % 2 == 1 {
        s[start] as int + sum_odd(s, start + 1, end)
    } else {
        sum_odd(s, start + 1, end)
    }
}

pub open spec fn even_sum_after_removal(s: Seq<i32>, i: int) -> int {
    sum_even(s, 0, i) + sum_odd(s, i + 1, s.len() as int)
}

pub open spec fn odd_sum_after_removal(s: Seq<i32>, i: int) -> int {
    sum_odd(s, 0, i) + sum_even(s, i + 1, s.len() as int)
}

pub open spec fn is_fair_after_removal(s: Seq<i32>, i: int) -> bool {
    even_sum_after_removal(s, i) == odd_sum_after_removal(s, i)
}

pub open spec fn count_fair(s: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        0
    } else if is_fair_after_removal(s, start) {
        1 + count_fair(s, start + 1, end)
    } else {
        count_fair(s, start + 1, end)
    }
}

proof fn lemma_sum_even_bounds(s: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall |i: int| start <= i < end ==> 1 <= #[trigger] s[i] <= 10_000,
    ensures
        0 <= sum_even(s, start, end) <= (end - start) * 10_000,
    decreases end - start,
{
    if start < end {
        lemma_sum_even_bounds(s, start + 1, end);
        assert((end - start - 1) * 10_000 + 10_000 <= (end - start) * 10_000) by(nonlinear_arith)
            requires end - start >= 1;
    }
}

proof fn lemma_sum_odd_bounds(s: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall |i: int| start <= i < end ==> 1 <= #[trigger] s[i] <= 10_000,
    ensures
        0 <= sum_odd(s, start, end) <= (end - start) * 10_000,
    decreases end - start,
{
    if start < end {
        lemma_sum_odd_bounds(s, start + 1, end);
        assert((end - start - 1) * 10_000 + 10_000 <= (end - start) * 10_000) by(nonlinear_arith)
            requires end - start >= 1;
    }
}

proof fn lemma_sum_even_split(s: Seq<i32>, start: int, mid: int, end: int)
    requires
        0 <= start <= mid <= end <= s.len(),
    ensures
        sum_even(s, start, end) == sum_even(s, start, mid) + sum_even(s, mid, end),
    decreases mid - start,
{
    if start < mid {
        lemma_sum_even_split(s, start + 1, mid, end);
    }
}

proof fn lemma_sum_odd_split(s: Seq<i32>, start: int, mid: int, end: int)
    requires
        0 <= start <= mid <= end <= s.len(),
    ensures
        sum_odd(s, start, end) == sum_odd(s, start, mid) + sum_odd(s, mid, end),
    decreases mid - start,
{
    if start < mid {
        lemma_sum_odd_split(s, start + 1, mid, end);
    }
}

proof fn lemma_sum_even_single(s: Seq<i32>, k: int)
    requires
        0 <= k,
        k + 1 <= s.len(),
    ensures
        sum_even(s, k, k + 1) == if k % 2 == 0 { s[k] as int } else { 0 as int },
{
    assert(sum_even(s, k + 1, k + 1) == 0 as int);
}

proof fn lemma_sum_odd_single(s: Seq<i32>, k: int)
    requires
        0 <= k,
        k + 1 <= s.len(),
    ensures
        sum_odd(s, k, k + 1) == if k % 2 == 1 { s[k] as int } else { 0 as int },
{
    assert(sum_odd(s, k + 1, k + 1) == 0 as int);
}

proof fn lemma_count_fair_nonneg(s: Seq<i32>, start: int, end: int)
    ensures
        count_fair(s, start, end) >= 0,
    decreases end - start,
{
    if start < end {
        lemma_count_fair_nonneg(s, start + 1, end);
    }
}

proof fn lemma_count_fair_upper(s: Seq<i32>, start: int, end: int)
    requires
        start <= end,
    ensures
        count_fair(s, start, end) <= end - start,
    decreases end - start,
{
    if start < end {
        lemma_count_fair_upper(s, start + 1, end);
    }
}

impl Solution {
    pub fn ways_to_make_fair(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            res == count_fair(nums@, 0, nums@.len() as int),
    {
        let n = nums.len();
        let mut right_even: i64 = 0;
        let mut right_odd: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                n <= 100_000,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] nums[k] <= 10_000,
                right_even == sum_even(nums@, 0, i as int),
                right_odd == sum_odd(nums@, 0, i as int),
                0 <= right_even <= n as int * 10_000,
                0 <= right_odd <= n as int * 10_000,
            decreases n - i,
        {
            proof {
                lemma_sum_even_single(nums@, i as int);
                lemma_sum_odd_single(nums@, i as int);
                lemma_sum_even_split(nums@, 0, i as int, i as int + 1);
                lemma_sum_odd_split(nums@, 0, i as int, i as int + 1);
                lemma_sum_even_bounds(nums@, 0, i as int + 1);
                lemma_sum_odd_bounds(nums@, 0, i as int + 1);
                assert((i as int + 1) * 10_000 <= n as int * 10_000) by(nonlinear_arith)
                    requires 0 <= i as int + 1 <= n as int;
            }
            if i % 2 == 0 {
                right_even = right_even + nums[i] as i64;
            } else {
                right_odd = right_odd + nums[i] as i64;
            }
            i = i + 1;
        }
        let mut left_even: i64 = 0;
        let mut left_odd: i64 = 0;
        let mut result: i32 = 0;
        i = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                n <= 100_000,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] nums[k] <= 10_000,
                left_even == sum_even(nums@, 0, i as int),
                left_odd == sum_odd(nums@, 0, i as int),
                right_even == sum_even(nums@, i as int, n as int),
                right_odd == sum_odd(nums@, i as int, n as int),
                result as int + count_fair(nums@, i as int, n as int) == count_fair(nums@, 0, n as int),
                0 <= left_even <= n as int * 10_000,
                0 <= left_odd <= n as int * 10_000,
                0 <= right_even <= n as int * 10_000,
                0 <= right_odd <= n as int * 10_000,
                0 <= result,
                result as int <= n as int,
            decreases n - i,
        {
            proof {
                lemma_sum_even_single(nums@, i as int);
                lemma_sum_odd_single(nums@, i as int);
                lemma_sum_even_split(nums@, i as int, i as int + 1, n as int);
                lemma_sum_odd_split(nums@, i as int, i as int + 1, n as int);
                lemma_sum_even_bounds(nums@, i as int + 1, n as int);
                lemma_sum_odd_bounds(nums@, i as int + 1, n as int);
                assert((n as int - i as int - 1) * 10_000 <= n as int * 10_000) by(nonlinear_arith)
                    requires 0 <= n as int - i as int - 1 <= n as int;
            }
            if i % 2 == 0 {
                right_even = right_even - nums[i] as i64;
            } else {
                right_odd = right_odd - nums[i] as i64;
            }
            proof {
                assert(right_even == sum_even(nums@, i as int + 1, n as int));
                assert(right_odd == sum_odd(nums@, i as int + 1, n as int));
                assert(even_sum_after_removal(nums@, i as int) == left_even + right_odd);
                assert(odd_sum_after_removal(nums@, i as int) == left_odd + right_even);
                lemma_count_fair_nonneg(nums@, i as int + 1, n as int);
                lemma_count_fair_upper(nums@, i as int + 1, n as int);
            }
            if left_even + right_odd == left_odd + right_even {
                proof {
                    assert(is_fair_after_removal(nums@, i as int));
                    assert(count_fair(nums@, i as int, n as int) == 1 + count_fair(nums@, i as int + 1, n as int));
                }
                result = result + 1;
            } else {
                proof {
                    assert(!is_fair_after_removal(nums@, i as int));
                    assert(count_fair(nums@, i as int, n as int) == count_fair(nums@, i as int + 1, n as int));
                }
            }
            proof {
                lemma_sum_even_split(nums@, 0, i as int, i as int + 1);
                lemma_sum_odd_split(nums@, 0, i as int, i as int + 1);
                lemma_sum_even_bounds(nums@, 0, i as int + 1);
                lemma_sum_odd_bounds(nums@, 0, i as int + 1);
                assert((i as int + 1) * 10_000 <= n as int * 10_000) by(nonlinear_arith)
                    requires 0 <= i as int + 1 <= n as int;
            }
            if i % 2 == 0 {
                left_even = left_even + nums[i] as i64;
            } else {
                left_odd = left_odd + nums[i] as i64;
            }
            proof {
                lemma_count_fair_upper(nums@, 0, n as int);
            }
            i = i + 1;
        }
        result
    }
}

}
