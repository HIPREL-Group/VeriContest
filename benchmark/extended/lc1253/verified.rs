use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_value_prefix(colsum: Seq<i32>, value: i32, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_value_prefix(colsum, value, end - 1) + if colsum[end - 1] == value { 1int } else { 0int }
    }
}

pub open spec fn sum_seq(row: Seq<i32>) -> int
    decreases row.len(),
{
    if row.len() == 0 {
        0
    } else {
        sum_seq(row.drop_last()) + row.last() as int
    }
}

pub open spec fn solution_possible(upper: int, lower: int, colsum: Seq<i32>) -> bool {
    let twos = count_value_prefix(colsum, 2, colsum.len() as int);
    let ones = count_value_prefix(colsum, 1, colsum.len() as int);
    twos <= upper && twos <= lower && upper - twos + lower - twos == ones
}

pub open spec fn valid_binary_rows(top: Seq<i32>, bottom: Seq<i32>, upper: int, lower: int, colsum: Seq<i32>) -> bool {
    &&& top.len() == colsum.len()
    &&& bottom.len() == colsum.len()
    &&& forall|i: int| 0 <= i < colsum.len() ==> {
        &&& #[trigger] top[i] == 0 || #[trigger] top[i] == 1
        &&& #[trigger] bottom[i] == 0 || #[trigger] bottom[i] == 1
        &&& top[i] + bottom[i] == colsum[i]
    }
    &&& sum_seq(top) == upper
    &&& sum_seq(bottom) == lower
}

pub open spec fn min_int(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

proof fn lemma_sum_push(row: Seq<i32>, value: i32)
    ensures
        sum_seq(row.push(value)) == sum_seq(row) + value as int,
{
    assert(row.push(value).drop_last() =~= row);
}

proof fn lemma_count_value_prefix_step(colsum: Seq<i32>, value: i32, end: int)
    requires
        0 <= end < colsum.len(),
    ensures
        count_value_prefix(colsum, value, end + 1)
            == count_value_prefix(colsum, value, end)
                + if colsum[end] == value { 1int } else { 0int },
{
}

proof fn lemma_min_progress(a: int, b: int)
    requires
        0 <= a,
        0 <= b,
    ensures
        min_int(a + 1, b) == if a < b { min_int(a, b) + 1 } else { min_int(a, b) },
{
}

impl Solution {
    pub fn reconstruct_matrix(upper: i32, lower: i32, colsum: Vec<i32>) -> (result: Vec<Vec<i32>>)
        requires
            1 <= colsum.len() <= 100_000,
            0 <= upper <= colsum.len(),
            0 <= lower <= colsum.len(),
            forall|i: int| 0 <= i < colsum.len() ==> 0 <= #[trigger] colsum[i] <= 2,
        ensures
            result.len() == 0 || result.len() == 2,
            result.len() == 0 ==> !solution_possible(upper as int, lower as int, colsum@),
            result.len() == 2 ==> ({
                &&& result[0]@.len() == colsum.len()
                &&& result[1]@.len() == colsum.len()
                &&& forall|i: int| 0 <= i < colsum.len() ==> 0 <= #[trigger] result[0]@[i] <= 1
                &&& forall|i: int| 0 <= i < colsum.len() ==> 0 <= #[trigger] result[1]@[i] <= 1
                &&& forall|i: int| 0 <= i < colsum.len() ==> result[0]@[i] + result[1]@[i] == colsum[i]
                &&& sum_seq(result[0]@) == upper as int
                &&& sum_seq(result[1]@) == lower as int
            }),
    {
        let n = colsum.len();
        let mut ones: i32 = 0;
        let mut twos: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == colsum.len(),
                1 <= n <= 100_000,
                0 <= upper <= n,
                0 <= lower <= n,
                forall|k: int| 0 <= k < n ==> 0 <= #[trigger] colsum[k] <= 2,
                0 <= i <= n,
                ones as int == count_value_prefix(colsum@, 1, i as int),
                twos as int == count_value_prefix(colsum@, 2, i as int),
                0 <= ones <= i,
                0 <= twos <= i,
            decreases n - i,
        {
            proof {
                lemma_count_value_prefix_step(colsum@, 1, i as int);
                lemma_count_value_prefix_step(colsum@, 2, i as int);
            }
            if colsum[i] == 1 {
                ones += 1;
            } else if colsum[i] == 2 {
                twos += 1;
            }
            i += 1;
        }
        proof {
            assert(ones as int == count_value_prefix(colsum@, 1, n as int));
            assert(twos as int == count_value_prefix(colsum@, 2, n as int));
        }
        if twos > upper || twos > lower {
            proof {
                assert(count_value_prefix(colsum@, 2, colsum.len() as int) == twos as int);
            }
            return Vec::new();
        }
        let upper_ones = upper - twos;
        let lower_ones = lower - twos;
        if upper_ones + lower_ones != ones {
            proof {
                assert(count_value_prefix(colsum@, 1, colsum.len() as int) == ones as int);
                assert(count_value_prefix(colsum@, 2, colsum.len() as int) == twos as int);
            }
            return Vec::new();
        }
        let mut top: Vec<i32> = Vec::new();
        let mut bottom: Vec<i32> = Vec::new();
        let mut rem_upper_ones = upper_ones;
        let mut j: usize = 0;
        while j < n
            invariant
                n == colsum.len(),
                1 <= n <= 100_000,
                0 <= upper <= n,
                0 <= lower <= n,
                forall|k: int| 0 <= k < n ==> 0 <= #[trigger] colsum[k] <= 2,
                twos as int == count_value_prefix(colsum@, 2, n as int),
                ones as int == count_value_prefix(colsum@, 1, n as int),
                0 <= upper_ones <= upper,
                0 <= lower_ones <= lower,
                upper_ones + lower_ones == ones,
                0 <= j <= n,
                top.len() == j,
                bottom.len() == j,
                0 <= rem_upper_ones <= upper_ones,
                upper_ones as int - rem_upper_ones as int == min_int(count_value_prefix(colsum@, 1, j as int), upper_ones as int),
                sum_seq(top@) + rem_upper_ones as int == count_value_prefix(colsum@, 2, j as int) + upper_ones as int,
                sum_seq(bottom@) == count_value_prefix(colsum@, 2, j as int) + count_value_prefix(colsum@, 1, j as int) - upper_ones as int + rem_upper_ones as int,
                forall|k: int| 0 <= k < j ==> 0 <= #[trigger] top@[k] <= 1,
                forall|k: int| 0 <= k < j ==> 0 <= #[trigger] bottom@[k] <= 1,
                forall|k: int| 0 <= k < j ==> top@[k] + bottom@[k] == colsum[k],
            decreases n - j,
        {
            proof {
                lemma_count_value_prefix_step(colsum@, 1, j as int);
                lemma_count_value_prefix_step(colsum@, 2, j as int);
                lemma_min_progress(count_value_prefix(colsum@, 1, j as int), upper_ones as int);
            }
            let ghost old_top = top@;
            let ghost old_bottom = bottom@;
            let ghost old_rem = rem_upper_ones;
            if colsum[j] == 2 {
                top.push(1);
                bottom.push(1);
                proof {
                    lemma_sum_push(old_top, 1);
                    lemma_sum_push(old_bottom, 1);
                    assert(top@ == old_top.push(1));
                    assert(bottom@ == old_bottom.push(1));
                }
            } else if colsum[j] == 1 {
                if rem_upper_ones > 0 {
                    top.push(1);
                    bottom.push(0);
                    rem_upper_ones -= 1;
                    proof {
                        lemma_sum_push(old_top, 1);
                        lemma_sum_push(old_bottom, 0);
                        assert(top@ == old_top.push(1));
                        assert(bottom@ == old_bottom.push(0));
                    }
                } else {
                    top.push(0);
                    bottom.push(1);
                    proof {
                        lemma_sum_push(old_top, 0);
                        lemma_sum_push(old_bottom, 1);
                        assert(top@ == old_top.push(0));
                        assert(bottom@ == old_bottom.push(1));
                    }
                }
            } else {
                top.push(0);
                bottom.push(0);
                proof {
                    lemma_sum_push(old_top, 0);
                    lemma_sum_push(old_bottom, 0);
                    assert(top@ == old_top.push(0));
                    assert(bottom@ == old_bottom.push(0));
                }
            }
            j += 1;
        }
        proof {
            assert(j == n);
            assert(count_value_prefix(colsum@, 1, n as int) == ones as int);
            assert(lower_ones >= 0);
            assert(upper_ones as int <= count_value_prefix(colsum@, 1, n as int)) by {
                assert(upper_ones as int + lower_ones as int == ones as int);
                assert(count_value_prefix(colsum@, 1, n as int) == ones as int);
            }
            assert(min_int(count_value_prefix(colsum@, 1, n as int), upper_ones as int) == upper_ones as int);
            assert(upper_ones as int - rem_upper_ones as int == upper_ones as int);
            assert(rem_upper_ones == 0);
            assert(sum_seq(top@) == twos as int + upper_ones as int);
            assert(sum_seq(bottom@) == twos as int + ones as int - upper_ones as int);
            assert(sum_seq(top@) == upper as int);
            assert(sum_seq(bottom@) == lower as int);
        }
        let mut result: Vec<Vec<i32>> = Vec::new();
        result.push(top);
        result.push(bottom);
        proof {
            assert(result.len() == 2);
            assert(result@[0]@ == top@);
            assert(result@[1]@ == bottom@);
            assert forall|idx: int| 0 <= idx < colsum.len() implies 0 <= #[trigger] top@[idx] <= 1 by {
                assert(0 <= idx < j as int);
                assert(0 <= top@[idx] <= 1);
            };
            assert forall|idx: int| 0 <= idx < colsum.len() implies 0 <= #[trigger] bottom@[idx] <= 1 by {
                assert(0 <= idx < j as int);
                assert(0 <= bottom@[idx] <= 1);
            };
            assert forall|idx: int| 0 <= idx < colsum.len() implies top@[idx] + bottom@[idx] == colsum[idx] by {
                assert(0 <= idx < j as int);
                assert(top@[idx] + bottom@[idx] == colsum[idx]);
            };
            assert forall|idx: int| 0 <= idx < colsum.len() implies 0 <= #[trigger] result@[0]@[idx] <= 1 by {
                assert(result@[0]@[idx] == top@[idx]);
                assert(0 <= top@[idx] <= 1);
            };
            assert forall|idx: int| 0 <= idx < colsum.len() implies 0 <= #[trigger] result@[1]@[idx] <= 1 by {
                assert(result@[1]@[idx] == bottom@[idx]);
                assert(0 <= bottom@[idx] <= 1);
            };
            assert forall|idx: int| 0 <= idx < colsum.len() implies result@[0]@[idx] + result@[1]@[idx] == colsum[idx] by {
                assert(result@[0]@[idx] == top@[idx]);
                assert(result@[1]@[idx] == bottom@[idx]);
                assert(top@[idx] + bottom@[idx] == colsum[idx]);
            };
        }
        result
    }
}

}
