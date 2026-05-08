use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn zero_run_len_ending_at(a: Seq<i32>, i: int) -> int
    decreases i + 1,
{
    if i < 0 || i >= a.len() {
        0
    } else if a[i] != 0 {
        0
    } else if i == 0 {
        1
    } else if a[i - 1] == 0 {
        zero_run_len_ending_at(a, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn max_zero_run_upto(a: Seq<i32>, hi: int) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        let e = zero_run_len_ending_at(a, hi);
        let prev = max_zero_run_upto(a, hi - 1);
        if e > prev {
            e
        } else {
            prev
        }
    }
}

proof fn lemma_max_zero_upto_nonneg(a: Seq<i32>, hi: int)
    requires
        hi >= -1,
    ensures
        max_zero_run_upto(a, hi) >= 0,
    decreases hi + 1,
{
    if hi < 0 {
        assert(max_zero_run_upto(a, hi) == 0);
    } else {
        lemma_max_zero_upto_nonneg(a, hi - 1);
        assert(max_zero_run_upto(a, hi) >= 0);
    }
}

proof fn lemma_max_upto_ge_zero_run(a: Seq<i32>, hi: int, j: int)
    requires
        0 <= j <= hi,
    ensures
        zero_run_len_ending_at(a, j) <= max_zero_run_upto(a, hi),
    decreases hi - j,
{
    if j == hi {
        assert(max_zero_run_upto(a, hi) >= zero_run_len_ending_at(a, hi));
    } else {
        lemma_max_upto_ge_zero_run(a, hi - 1, j);
        assert(max_zero_run_upto(a, hi) >= max_zero_run_upto(a, hi - 1));
    }
}

proof fn lemma_zero_run_len_le_index(a: Seq<i32>, idx: int)
    requires
        0 <= idx < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[j] == 0 || a[j] == 1,
    ensures
        zero_run_len_ending_at(a, idx) <= idx + 1,
    decreases idx + 1,
{
    if idx == 0 {
    } else {
        lemma_zero_run_len_le_index(a, idx - 1);
        if a[idx] != 0 {
        } else if a[idx - 1] == 0 {
            assert(zero_run_len_ending_at(a, idx) == zero_run_len_ending_at(a, idx - 1) + 1);
            assert(zero_run_len_ending_at(a, idx - 1) <= idx);
        } else {
        }
    }
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn longest_blank_space(a: &Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() && a.len() <= 100,
            forall|j: int|
                0 <= j < a.len() ==> #[trigger] a[j] == 0 || a[j] == 1,
        ensures
            0 <= result as int,
            result as int == max_zero_run_upto(a@, (a.len() as int) - 1),
    {
        let n = a.len();
        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut i: usize = 0;
        proof {
            reveal_with_fuel(zero_run_len_ending_at, 5);
            reveal_with_fuel(max_zero_run_upto, 5);
            assert(zero_run_len_ending_at(a@, -1) == 0);
            assert(max_zero_run_upto(a@, -1) == 0);
            assert(cur as int == zero_run_len_ending_at(a@, (i as int) - 1));
            assert(best as int == max_zero_run_upto(a@, (i as int) - 1));
        }
        while i < n
            invariant
                1 <= a.len() && a.len() <= 100,
                n == a.len(),
                forall|j: int|
                    0 <= j < a.len() as int ==> #[trigger] a[j] == 0 || a[j] == 1,
                i <= n,
                cur as int == zero_run_len_ending_at(a@, (i as int) - 1),
                best as int == max_zero_run_upto(a@, (i as int) - 1),
                cur as int <= (i as int) + 1,
                best as int <= (i as int) + 1,
                0 <= cur as int && 0 <= best as int,
            decreases n - i,
        {
            if a[i] == 0 {
                cur = cur + 1;
            } else {
                cur = 0;
            }
            if cur > best {
                best = cur;
            } else {
            }
            proof {
                reveal_with_fuel(zero_run_len_ending_at, 5);
                assert(cur as int == zero_run_len_ending_at(a@, i as int));
                lemma_zero_run_len_le_index(a@, i as int);
                let e = zero_run_len_ending_at(a@, i as int);
                let pm = max_zero_run_upto(a@, (i as int) - 1);
                reveal_with_fuel(max_zero_run_upto, 5);
                assert(max_zero_run_upto(a@, i as int) == if e > pm { e } else { pm });
                assert(best as int == max_zero_run_upto(a@, i as int));
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(best as int == max_zero_run_upto(a@, (n as int) - 1));
            lemma_max_zero_upto_nonneg(a@, (a.len() as int) - 1);
        }
        best
    }
}

}
