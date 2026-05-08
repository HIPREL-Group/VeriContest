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

proof fn lemma_count_2s_extend_end(arr: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end,
        end < arr.len(),
    ensures
        count_2s_between(arr, start, end)
            == count_2s_between(arr, start, end - 1)
                + (if arr[end] == 2 { 1int } else { 0int }),
    decreases end - start,
{
    reveal_with_fuel(count_2s_between, 3);
    if start < end {
        lemma_count_2s_extend_end(arr, start + 1, end);
    }
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

        proof {
            lemma_small_mod(0nat, 998244353nat);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                3 <= n <= 200_000,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] a[k] <= 3,
                result as int == count_beautiful_subsequences_upto(a@, i as int) % 998244353,
                0 <= result < 998244353,
            decreases n - i,
        {
            if a[i] == 3 && i >= 2 {
                let ghost base_count = count_beautiful_subsequences_upto(a@, i as int);
                let mut j: usize = 0;
                let ghost mut partial_sum: int = 0;

                while j < i
                    invariant
                        0 <= j <= i,
                        2 <= i < n,
                        n == a.len(),
                        n <= 200_000,
                        forall |k: int| 0 <= k < n ==> 1 <= #[trigger] a[k] <= 3,
                        a@[i as int] == 3,
                        base_count == count_beautiful_subsequences_upto(a@, i as int),
                        partial_sum == (if j > 0 {
                            count_beautiful_subsequences_ending_at_helper(
                                a@, i as int, j as int - 1,
                            )
                        } else {
                            0
                        }),
                        result as int == (base_count + partial_sum) % 998244353,
                        0 <= result < 998244353,
                    decreases i - j,
                {
                    if a[j] == 1 {
                        let mut count_2s: u32 = 0;
                        let mut k: usize = j + 1;
                        while k < i
                            invariant
                                j + 1 <= k <= i,
                                i < n,
                                n == a.len(),
                                n <= 200_000,
                                forall |idx: int| 0 <= idx < n ==>
                                    1 <= #[trigger] a[idx] <= 3,
                                count_2s as int == count_2s_between(
                                    a@, j as int + 1, k as int - 1,
                                ),
                                count_2s as usize + j + 1 <= k,
                            decreases i - k,
                        {
                            proof {
                                lemma_count_2s_extend_end(a@, j as int + 1, k as int);
                            }
                            if a[k] == 2 {
                                count_2s += 1;
                            }
                            k += 1;
                        }

                        let mut ways: u64 = 1;
                        let mut exp: u32 = 0;
                        proof {
                            reveal_with_fuel(pow2, 2);
                            lemma_small_mod(1nat, 998244353nat);
                        }
                        proof {
                            assert(count_2s as usize + j + 1 <= i);
                            assert(count_2s as usize <= i);
                        }
                        while exp < count_2s
                            invariant
                                0 <= exp <= count_2s,
                                count_2s as usize <= i,
                                i < n,
                                n <= 200_000,
                                ways as int == pow2(exp as int) % 998244353,
                                0 <= ways < 998244353u64,
                            decreases count_2s - exp,
                        {
                            proof {
                                reveal_with_fuel(pow2, 2);
                                assert(pow2(exp as int + 1) == 2 * pow2(exp as int));
                                lemma_mul_mod_noop_left(pow2(exp as int), 2, 998244353);
                                lemma_mod_bound(2 * pow2(exp as int), 998244353);
                            }
                            ways = (ways * 2) % 998244353u64;
                            exp += 1;
                        }

                        let contrib = (((ways as u128) + 998244353u128 - 1)
                            % 998244353u128) as u64;

                        proof {
                            let p2 = pow2(count_2s_between(
                                a@, j as int + 1, i as int - 1,
                            ));
                            assert(ways as int == p2 % 998244353);
                            assert(contrib as int == (p2 - 1) % 998244353);

                            lemma_add_mod_noop(
                                base_count + partial_sum, p2 - 1, 998244353,
                            );

                            let neg1: int = -1;
                            if j == 0 {
                                reveal_with_fuel(
                                    count_beautiful_subsequences_ending_at_helper, 2,
                                );
                                assert(
                                    count_beautiful_subsequences_ending_at_helper(
                                        a@, i as int, neg1,
                                    ) == 0
                                );
                            }
                            assert(
                                count_beautiful_subsequences_ending_at_helper(
                                    a@, i as int, j as int,
                                ) == partial_sum + (p2 - 1)
                            );
                        }
                        result = (result + contrib) % 998244353u64;
                        proof {
                            partial_sum = partial_sum + (pow2(count_2s_between(
                                a@, j as int + 1, i as int - 1,
                            )) - 1);
                        }
                    } else {
                        proof {
                            let neg1: int = -1;
                            if j == 0 {
                                reveal_with_fuel(
                                    count_beautiful_subsequences_ending_at_helper, 2,
                                );
                                assert(
                                    count_beautiful_subsequences_ending_at_helper(
                                        a@, i as int, neg1,
                                    ) == 0
                                );
                            }
                            assert(
                                count_beautiful_subsequences_ending_at_helper(
                                    a@, i as int, j as int,
                                ) == partial_sum
                            );
                        }
                    }
                    j += 1;
                }

                proof {
                    assert(partial_sum
                        == count_beautiful_subsequences_ending_at_helper(
                            a@, i as int, i as int - 1,
                        ));
                    assert(count_beautiful_subsequences_ending_at(a@, i as int)
                        == count_beautiful_subsequences_ending_at_helper(
                            a@, i as int, i as int - 1,
                        ));
                    assert(count_beautiful_subsequences_upto(a@, i as int + 1)
                        == base_count
                            + count_beautiful_subsequences_ending_at(a@, i as int));
                }
            } else {
                proof {
                    if i as int + 1 > 2 {
                        assert(count_beautiful_subsequences_upto(a@, i as int + 1)
                            == count_beautiful_subsequences_upto(a@, i as int));
                    }
                }
            }
            i += 1;
        }

        result
    }
}

}
