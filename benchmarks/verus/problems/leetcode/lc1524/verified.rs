use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

fn main() {}

verus! {

pub struct Solution;

pub open spec fn subarray_sum(s: Seq<i32>, i: int, j: int) -> int
    decreases j - i + 1,
{
    if i > j { 0 }
    else { subarray_sum(s, i, j - 1) + s[j] as int }
}

pub open spec fn count_odd_ending(s: Seq<i32>, end_idx: int, k: int) -> int
    decreases k + 1,
{
    if k < 0 { 0 }
    else {
        count_odd_ending(s, end_idx, k - 1)
        + if subarray_sum(s, k, end_idx) % 2 != 0 { 1 as int } else { 0 as int }
    }
}

pub open spec fn count_even_ending(s: Seq<i32>, end_idx: int, k: int) -> int
    decreases k + 1,
{
    if k < 0 { 0 }
    else {
        count_even_ending(s, end_idx, k - 1)
        + if subarray_sum(s, k, end_idx) % 2 == 0 { 1 as int } else { 0 as int }
    }
}

pub open spec fn count_odd_subarrays(s: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else {
        count_odd_subarrays(s, n - 1) + count_odd_ending(s, n - 1, n - 1)
    }
}

proof fn lemma_subarray_sum_last(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j,
        j < s.len() as int,
    ensures
        subarray_sum(s, i, j) == subarray_sum(s, i, j - 1) + s[j] as int,
{
}

proof fn lemma_subarray_sum_positive(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j,
        j < s.len() as int,
        forall |k: int| 0 <= k < s.len() ==> 1 <= #[trigger] s[k] <= 100,
    ensures
        subarray_sum(s, i, j) >= 1,
    decreases j - i + 1,
{
    if i < j {
        lemma_subarray_sum_positive(s, i, j - 1);
    } else {
        assert(subarray_sum(s, j, j - 1) == 0);
    }
}

proof fn lemma_shift_even(s: Seq<i32>, j: int, k: int)
    requires
        0 < j,
        j < s.len() as int,
        -1 <= k <= j - 1,
        s[j] as int % 2 == 0,
        forall |idx: int| 0 <= idx < s.len() ==> 1 <= #[trigger] s[idx] <= 100,
    ensures
        count_odd_ending(s, j, k) == count_odd_ending(s, j - 1, k),
        count_even_ending(s, j, k) == count_even_ending(s, j - 1, k),
    decreases k + 1,
{
    if k >= 0 {
        lemma_shift_even(s, j, k - 1);
        lemma_subarray_sum_last(s, k, j);
        lemma_subarray_sum_positive(s, k, j - 1);
        assert((subarray_sum(s, k, j - 1) + s[j] as int) % 2
            == subarray_sum(s, k, j - 1) % 2) by(nonlinear_arith)
            requires
                subarray_sum(s, k, j - 1) >= 1,
                s[j] as int >= 1,
                s[j] as int % 2 == 0,
        ;
    }
}

proof fn lemma_shift_odd(s: Seq<i32>, j: int, k: int)
    requires
        0 < j,
        j < s.len() as int,
        -1 <= k <= j - 1,
        s[j] as int % 2 != 0,
        forall |idx: int| 0 <= idx < s.len() ==> 1 <= #[trigger] s[idx] <= 100,
    ensures
        count_odd_ending(s, j, k) == count_even_ending(s, j - 1, k),
        count_even_ending(s, j, k) == count_odd_ending(s, j - 1, k),
    decreases k + 1,
{
    if k >= 0 {
        lemma_shift_odd(s, j, k - 1);
        lemma_subarray_sum_last(s, k, j);
        lemma_subarray_sum_positive(s, k, j - 1);
        assert((subarray_sum(s, k, j - 1) + s[j] as int) % 2
            != subarray_sum(s, k, j - 1) % 2) by(nonlinear_arith)
            requires
                subarray_sum(s, k, j - 1) >= 1,
                s[j] as int >= 1,
                s[j] as int % 2 != 0,
        ;
    }
}

proof fn lemma_transition_even(s: Seq<i32>, j: int)
    requires
        0 < j,
        j < s.len() as int,
        s[j] as int % 2 == 0,
        forall |idx: int| 0 <= idx < s.len() ==> 1 <= #[trigger] s[idx] <= 100,
    ensures
        count_odd_ending(s, j, j) == count_odd_ending(s, j - 1, j - 1),
        count_even_ending(s, j, j) == count_even_ending(s, j - 1, j - 1) + 1,
{
    lemma_shift_even(s, j, j - 1);
    assert(subarray_sum(s, j, j) == subarray_sum(s, j, j - 1) + s[j] as int);
    assert(subarray_sum(s, j, j - 1) == 0);
}

proof fn lemma_transition_odd(s: Seq<i32>, j: int)
    requires
        0 < j,
        j < s.len() as int,
        s[j] as int % 2 != 0,
        forall |idx: int| 0 <= idx < s.len() ==> 1 <= #[trigger] s[idx] <= 100,
    ensures
        count_odd_ending(s, j, j) == count_even_ending(s, j - 1, j - 1) + 1,
        count_even_ending(s, j, j) == count_odd_ending(s, j - 1, j - 1),
{
    lemma_shift_odd(s, j, j - 1);
    assert(subarray_sum(s, j, j) == subarray_sum(s, j, j - 1) + s[j] as int);
    assert(subarray_sum(s, j, j - 1) == 0);
}

proof fn lemma_odd_even_sum(s: Seq<i32>, end_idx: int, k: int)
    requires
        -1 <= k <= end_idx,
        end_idx < s.len() as int,
    ensures
        count_odd_ending(s, end_idx, k) + count_even_ending(s, end_idx, k) == k + 1,
    decreases k + 1,
{
    if k >= 0 {
        lemma_odd_even_sum(s, end_idx, k - 1);
    }
}

proof fn lemma_count_nonneg(s: Seq<i32>, end_idx: int, k: int)
    ensures
        count_odd_ending(s, end_idx, k) >= 0,
        count_even_ending(s, end_idx, k) >= 0,
    decreases k + 1,
{
    if k >= 0 {
        lemma_count_nonneg(s, end_idx, k - 1);
    }
}

proof fn lemma_count_odd_subarrays_nonneg(s: Seq<i32>, n: int)
    ensures
        count_odd_subarrays(s, n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_count_odd_subarrays_nonneg(s, n - 1);
        lemma_count_nonneg(s, n - 1, n - 1);
    }
}

proof fn lemma_mod_add(a: int, b: int, m: int)
    requires
        m > 0,
        a >= 0,
        b >= 0,
    ensures
        (a % m + b) % m == (a + b) % m,
{
    lemma_fundamental_div_mod(a, m);
    lemma_mod_multiples_vanish(a / m, a % m + b, m);
}

impl Solution {
    pub fn num_of_subarrays(arr: Vec<i32>) -> (res: i32)
        requires
            1 <= arr.len() <= 100_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100,
        ensures
            0 <= res < 1_000_000_007,
            res as int == count_odd_subarrays(arr@, arr.len() as int) % 1_000_000_007,
    {
        let mut odd: i64 = 0;
        let mut even: i64 = 0;
        let mut res: i64 = 0;
        let mut i: usize = 0;
        while i < arr.len()
            invariant
                0 <= i <= arr.len(),
                1 <= arr.len() <= 100_000,
                forall |k: int| 0 <= k < arr.len() ==> 1 <= #[trigger] arr[k] <= 100,
                i == 0 ==> (odd == 0 && even == 0),
                i > 0 ==> odd as int == count_odd_ending(arr@, (i - 1) as int, (i - 1) as int),
                i > 0 ==> even as int == count_even_ending(arr@, (i - 1) as int, (i - 1) as int),
                0 <= odd as int <= i as int,
                0 <= even as int <= i as int,
                odd as int + even as int == i as int,
                0 <= res < 1_000_000_007,
                res as int == count_odd_subarrays(arr@, i as int) % 1_000_000_007,
            decreases arr.len() - i,
        {
            if arr[i] % 2 == 0 {
                even = even + 1;
                proof {
                    if i > 0 {
                        lemma_transition_even(arr@, i as int);
                    } else {
                        assert(subarray_sum(arr@, 0, -1 as int) == 0);
                        assert(count_odd_ending(arr@, 0, -1 as int) == 0);
                        assert(count_even_ending(arr@, 0, -1 as int) == 0);
                    }
                    assert(odd as int == count_odd_ending(arr@, i as int, i as int));
                    assert(even as int == count_even_ending(arr@, i as int, i as int));
                }
            } else {
                let tmp = odd;
                odd = even + 1;
                even = tmp;
                proof {
                    if i > 0 {
                        lemma_transition_odd(arr@, i as int);
                    } else {
                        assert(subarray_sum(arr@, 0, -1 as int) == 0);
                        assert(count_odd_ending(arr@, 0, -1 as int) == 0);
                        assert(count_even_ending(arr@, 0, -1 as int) == 0);
                    }
                    assert(odd as int == count_odd_ending(arr@, i as int, i as int));
                    assert(even as int == count_even_ending(arr@, i as int, i as int));
                }
            }
            proof {
                lemma_odd_even_sum(arr@, i as int, i as int);
                lemma_count_nonneg(arr@, i as int, i as int);
                lemma_count_odd_subarrays_nonneg(arr@, i as int);
                assert(0 <= odd as int <= i as int + 1);
                assert(0 <= even as int <= i as int + 1);
                assert(odd as int + even as int == i as int + 1);
                lemma_mod_add(
                    count_odd_subarrays(arr@, i as int),
                    count_odd_ending(arr@, i as int, i as int),
                    1_000_000_007 as int,
                );
            }
            res = (res + odd) % 1_000_000_007i64;
            i = i + 1;
        }
        res as i32
    }
}

}
