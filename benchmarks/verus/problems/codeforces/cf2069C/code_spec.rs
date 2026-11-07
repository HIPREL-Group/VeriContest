use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_add_mod_noop, lemma_mul_mod_noop_left, lemma_mod_bound, lemma_small_mod,
};

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_beautiful_subsequence(seq: Seq<i32>) -> bool {
    &&& seq.len() >= 3
    &&& (forall |i: int| 1 <= i < seq.len() ==>
        (exists |j: int| 0 <= j < i && #[trigger] seq[j] < #[trigger] seq[i]))
    &&& (forall |i: int| 0 <= i < seq.len() - 1 ==>
        (exists |j: int| i < j < seq.len() && #[trigger] seq[i] < #[trigger] seq[j]))
}

pub open spec fn count_2s_between(arr: Seq<i32>, start: int, end: int) -> int
    recommends
        0 <= start <= end + 1,
        0 <= end < arr.len(),
    decreases end - start + 1,
{
    if start > end {
        0
    } else {
        let rest = count_2s_between(arr, start + 1, end);
        if arr[start] == 2 {
            1 + rest
        } else {
            rest
        }
    }
}

pub open spec fn pow2(n: int) -> int
    decreases n,
{
    if n <= 0 {
        1
    } else {
        2 * pow2(n - 1)
    }
}

pub open spec fn count_beautiful_subsequences_upto(arr: Seq<i32>, end: int) -> int
    recommends
        0 <= end <= arr.len(),
    decreases end,
{
    if end <= 2 {
        0
    } else {
        let prev = count_beautiful_subsequences_upto(arr, end - 1);
        if arr[end - 1] == 3 {
            prev + count_beautiful_subsequences_ending_at(arr, end - 1)
        } else {
            prev
        }
    }
}

pub open spec fn count_beautiful_subsequences_ending_at(arr: Seq<i32>, three_pos: int) -> int
    recommends
        2 <= three_pos < arr.len(),
        arr[three_pos] == 3,
    decreases three_pos,
{
    if three_pos < 2 {
        0
    } else {
        count_beautiful_subsequences_ending_at_helper(arr, three_pos, three_pos - 1)
    }
}

pub open spec fn count_beautiful_subsequences_ending_at_helper(
    arr: Seq<i32>, three_pos: int, one_candidate: int,
) -> int
    recommends
        2 <= three_pos < arr.len(),
        arr[three_pos] == 3,
        -1 <= one_candidate < three_pos,
    decreases one_candidate + 1,
{
    if one_candidate < 0 {
        0
    } else {
        let prev = count_beautiful_subsequences_ending_at_helper(
            arr, three_pos, one_candidate - 1,
        );
        if arr[one_candidate] == 1 {
            prev + (pow2(count_2s_between(arr, one_candidate + 1, three_pos - 1)) - 1)
        } else {
            prev
        }
    }
}

pub open spec fn count_beautiful_subsequences(arr: Seq<i32>) -> int {
    count_beautiful_subsequences_upto(arr, arr.len() as int)
}

impl Solution {
    pub fn count_beautiful_subsequences(a: Vec<i32>) -> (result: u64)
        requires
            3 <= a.len() <= 200_000,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 3,
        ensures
            result as int == count_beautiful_subsequences(a@) % 998244353,
    {
        let n = a.len();
        let mut result: u64 = 0;

        let mut i: usize = 0;
        while i < n
        {
            if a[i] == 3 && i >= 2 {
                let mut j: usize = 0;

                while j < i
                {
                    if a[j] == 1 {
                        let mut count_2s: u32 = 0;
                        let mut k: usize = j + 1;
                        while k < i
                        {
                            if a[k] == 2 {
                                count_2s += 1;
                            }
                            k += 1;
                        }

                        let mut ways: u64 = 1;
                        let mut exp: u32 = 0;
                        while exp < count_2s
                        {
                            ways = (ways * 2) % 998244353u64;
                            exp += 1;
                        }

                        let contrib = (((ways as u128) + 998244353u128 - 1)
                            % 998244353u128) as u64;

                        result = (result + contrib) % 998244353u64;
                    } else {
                    }
                    j += 1;
                }
            } else {
            }
            i += 1;
        }

        result
    }
}

}
