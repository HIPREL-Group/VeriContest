use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_nd_contiguous(seq: Seq<i64>, l: int, r: int) -> bool {
    &&& 0 <= l <= r < seq.len()
    &&& forall|k: int| l <= k < r ==> #[trigger] seq[k] <= seq[k + 1]
}

pub open spec fn run_len_ending_at(seq: Seq<i64>, i: int) -> int
    decreases i + 1,
{
    if i < 0 || i >= seq.len() {
        0
    } else if i == 0 {
        1
    } else if seq[i - 1] <= seq[i] {
        run_len_ending_at(seq, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn max_run_len_upto(seq: Seq<i64>, hi: int) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        let e = run_len_ending_at(seq, hi);
        let prev = max_run_len_upto(seq, hi - 1);
        if e > prev {
            e
        } else {
            prev
        }
    }
}

proof fn lemma_run_len_nonneg(seq: Seq<i64>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        run_len_ending_at(seq, i) >= 1,
    decreases i + 1,
{
    if i == 0 {
    } else {
        lemma_run_len_nonneg(seq, i - 1);
    }
}

proof fn lemma_segment_le_run_len(seq: Seq<i64>, l: int, r: int)
    requires
        0 <= l <= r < seq.len(),
        forall|k: int| l <= k < r ==> #[trigger] seq[k] <= seq[k + 1],
    ensures
        (r - l + 1) <= run_len_ending_at(seq, r),
    decreases r - l,
{
    if l == r {
        lemma_run_len_nonneg(seq, r);
        assert(r - l + 1 == 1);
    } else {
        assert(l < r);
        assert(seq[r - 1] <= seq[r]);
        assert(forall|k: int| l <= k < r - 1 ==> #[trigger] seq[k] <= seq[k + 1]);
        lemma_segment_le_run_len(seq, l, r - 1);
        assert(run_len_ending_at(seq, r) == run_len_ending_at(seq, r - 1) + 1);
        assert((r - l + 1) <= run_len_ending_at(seq, r));
    }
}

proof fn lemma_run_len_le_index(seq: Seq<i64>, idx: int)
    requires
        0 <= idx < seq.len(),
    ensures
        run_len_ending_at(seq, idx) <= idx + 1,
    decreases idx + 1,
{
    if idx == 0 {
        assert(run_len_ending_at(seq, 0) == 1);
    } else {
        lemma_run_len_le_index(seq, idx - 1);
        if seq[idx - 1] <= seq[idx] {
            assert(run_len_ending_at(seq, idx) == run_len_ending_at(seq, idx - 1) + 1);
            assert(run_len_ending_at(seq, idx - 1) <= idx);
            assert(run_len_ending_at(seq, idx) <= idx + 1);
        } else {
            assert(run_len_ending_at(seq, idx) == 1);
        }
    }
}

proof fn lemma_max_upto_ge_run_len(seq: Seq<i64>, hi: int, j: int)
    requires
        0 <= j <= hi,
    ensures
        run_len_ending_at(seq, j) <= max_run_len_upto(seq, hi),
    decreases hi - j,
{
    if j == hi {
        assert(max_run_len_upto(seq, hi) >= run_len_ending_at(seq, hi));
    } else {
        lemma_max_upto_ge_run_len(seq, hi - 1, j);
        assert(max_run_len_upto(seq, hi) >= max_run_len_upto(seq, hi - 1));
    }
}

proof fn lemma_nd_of_run_ending_at(seq: Seq<i64>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        is_nd_contiguous(seq, i - run_len_ending_at(seq, i) + 1, i),
    decreases i + 1,
{
    let rl = run_len_ending_at(seq, i);
    let l = i - rl + 1;
    if i == 0 {
        assert(rl == 1);
        assert(l == 0);
        assert(is_nd_contiguous(seq, 0, 0));
    } else {
        if seq[i - 1] <= seq[i] {
            assert(rl == run_len_ending_at(seq, i - 1) + 1);
            assert(l == (i - 1) - run_len_ending_at(seq, i - 1) + 1);
            lemma_nd_of_run_ending_at(seq, i - 1);
            assert(is_nd_contiguous(seq, l, i - 1));
            assert(forall|k: int| l <= k < i - 1 ==> #[trigger] seq[k] <= seq[k + 1]);
            assert(seq[i - 1] <= seq[i]);
            assert(is_nd_contiguous(seq, l, i));
        } else {
            assert(rl == 1);
            assert(l == i);
            assert(is_nd_contiguous(seq, i, i));
        }
    }
}

proof fn witness_end_for_max(seq: Seq<i64>, hi: int) -> (j: int)
    requires
        0 <= hi < seq.len(),
    ensures
        0 <= j <= hi,
        run_len_ending_at(seq, j) == max_run_len_upto(seq, hi),
    decreases hi,
{
    if hi == 0 {
        reveal_with_fuel(max_run_len_upto, 3);
        reveal_with_fuel(run_len_ending_at, 3);
        assert(run_len_ending_at(seq, 0) == 1);
        assert(max_run_len_upto(seq, 0) == run_len_ending_at(seq, 0));
        0
    } else {
        let e = run_len_ending_at(seq, hi);
        let pm = max_run_len_upto(seq, hi - 1);
        if e > pm {
            assert(max_run_len_upto(seq, hi) == e);
            assert(run_len_ending_at(seq, hi) == max_run_len_upto(seq, hi));
            hi
        } else {
            let j0 = witness_end_for_max(seq, hi - 1);
            j0
        }
    }
}

impl Solution {
    pub fn longest_non_decreasing_run(a: Vec<i64>) -> (result: usize)
        requires
            1 <= a.len() <= 100_000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            1 <= result as int <= a.len() as int,
            exists|l: int, r: int|
                0 <= l <= r < a.len() as int && is_nd_contiguous(a@, l, r) && r - l + 1 == result as int,
            forall|l: int, r: int|
                0 <= l <= r < a.len() as int && is_nd_contiguous(a@, l, r)
                    ==> r - l + 1 <= result as int,
    {
        let n = a.len();
        let mut best = 1usize;
        let mut cur = 1usize;
        let mut i = 1usize;
        proof {
            reveal_with_fuel(run_len_ending_at, 5);
            reveal_with_fuel(max_run_len_upto, 5);
            assert(run_len_ending_at(a@, 0) == 1);
            assert(max_run_len_upto(a@, 0) == 1);
            assert(cur as int == run_len_ending_at(a@, 0));
            assert(best as int == max_run_len_upto(a@, 0));
        }
        while i < n
            invariant
                1 <= n <= 100_000,
                n == a.len(),
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
                1 <= i <= n,
                cur <= n,
                best <= n,
                cur as int == run_len_ending_at(a@, i - 1),
                best as int == max_run_len_upto(a@, i - 1),
            decreases n - i,
        {
            proof {
                lemma_run_len_nonneg(a@, i - 1);
                lemma_run_len_le_index(a@, i - 1);
                assert(i as int <= n as int);
                assert((cur as int) + 1 <= n as int);
            }
            if a[i] >= a[i - 1] {
                assert(a@[(i - 1) as int] <= a@[i as int]);
                proof {
                    reveal_with_fuel(run_len_ending_at, 5);
                }
                assert(run_len_ending_at(a@, i as int) == run_len_ending_at(a@, i - 1) + 1);
                cur = cur + 1;
            } else {
                assert(!(a@[(i - 1) as int] <= a@[i as int]));
                proof {
                    reveal_with_fuel(run_len_ending_at, 5);
                }
                assert(run_len_ending_at(a@, i as int) == 1);
                cur = 1;
            }
            proof {
                reveal_with_fuel(run_len_ending_at, 5);
            }
            assert(cur as int == run_len_ending_at(a@, i as int));
            let ghost prev_best = best;
            if cur > best {
                best = cur;
            } else {
            }
            proof {
                reveal_with_fuel(max_run_len_upto, 5);
                assert(cur as int == run_len_ending_at(a@, i as int));
                assert(max_run_len_upto(a@, i as int)
                    == if run_len_ending_at(a@, i as int) > max_run_len_upto(a@, i - 1) {
                        run_len_ending_at(a@, i as int)
                    } else {
                        max_run_len_upto(a@, i - 1)
                    });
                if cur as int > prev_best as int {
                    assert(best as int == cur as int);
                } else {
                    assert(best as int == prev_best as int);
                }
            }
            assert(best as int == max_run_len_upto(a@, i as int));
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(best as int == max_run_len_upto(a@, n as int - 1));
            assert forall|l: int, r: int|
                (0 <= l <= r < a.len() as int && is_nd_contiguous(a@, l, r))
                    implies (r - l + 1) <= best as int by {
                assert forall|l: int, r: int|
                    (0 <= l <= r < a.len() as int && is_nd_contiguous(a@, l, r))
                        implies (r - l + 1) <= best as int by {
                    if 0 <= l <= r < a.len() as int && is_nd_contiguous(a@, l, r) {
                        lemma_segment_le_run_len(a@, l, r);
                        lemma_max_upto_ge_run_len(a@, n as int - 1, r);
                    }
                };
            };
            let jm = witness_end_for_max(a@, n as int - 1);
            let rl = run_len_ending_at(a@, jm);
            let lw = jm - rl + 1;
            lemma_nd_of_run_ending_at(a@, jm);
            assert(is_nd_contiguous(a@, lw, jm));
            assert(jm - lw + 1 == rl);
            assert(rl == max_run_len_upto(a@, n as int - 1));
            assert(rl == best as int);
        }
        best
    }
}

}
