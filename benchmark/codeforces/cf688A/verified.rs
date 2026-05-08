use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn all_opponents_present(row: Seq<u8>) -> bool {
    forall|j: int| 0 <= j && j < row.len() ==> #[trigger] row[j] == 49u8
}

pub open spec fn arya_beats(row: Seq<u8>) -> bool {
    !all_opponents_present(row)
}

pub open spec fn win_interval(days: Seq<Vec<u8>>, l: int, r: int) -> bool {
    forall|t: int| l <= t && t <= r ==> #[trigger] arya_beats(days[t]@)
}

pub open spec fn win_streak_ending_at(days: Seq<Vec<u8>>, i: int) -> int
    decreases i + 1,
{
    if i < 0 || i >= days.len() {
        0
    } else if !arya_beats(days[i]@) {
        0
    } else if i == 0 {
        1
    } else if arya_beats(days[i - 1]@) {
        win_streak_ending_at(days, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn max_win_streak_upto(days: Seq<Vec<u8>>, hi: int) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        let e = win_streak_ending_at(days, hi);
        let prev = max_win_streak_upto(days, hi - 1);
        if e > prev {
            e
        } else {
            prev
        }
    }
}

proof fn lemma_exists_zero_iff_beats(row: Seq<u8>)
    requires
        row.len() >= 1,
        forall|j: int| 0 <= j && j < row.len() ==> row[j] == 48u8 || row[j] == 49u8,
    ensures
        arya_beats(row) == (exists|k: int| 0 <= k && k < row.len() && #[trigger] row[k] == 48u8),
{
    assert(all_opponents_present(row) == (forall|j: int| 0 <= j && j < row.len() ==> row[j] == 49u8));
    if exists|k: int| 0 <= k && k < row.len() && row[k] == 48u8 {
        assert(!all_opponents_present(row));
        assert(arya_beats(row));
    } else {
        assert(forall|j: int| 0 <= j && j < row.len() ==> row[j] == 49u8);
        assert(all_opponents_present(row));
        assert(!arya_beats(row));
    }
}

proof fn lemma_win_streak_nonneg(days: Seq<Vec<u8>>, i: int)
    requires
        0 <= i < days.len(),
        arya_beats(days[i]@),
    ensures
        win_streak_ending_at(days, i) >= 1,
    decreases i + 1,
{
    if i == 0 {
    } else {
        if arya_beats(days[i - 1]@) {
            lemma_win_streak_nonneg(days, i - 1);
        } else {
        }
    }
}

proof fn lemma_segment_le_win_streak(days: Seq<Vec<u8>>, l: int, r: int)
    requires
        0 <= l <= r < days.len(),
        win_interval(days, l, r),
    ensures
        (r - l + 1) <= win_streak_ending_at(days, r),
    decreases r - l,
{
    if l == r {
        lemma_win_streak_nonneg(days, r);
        assert(r - l + 1 == 1);
    } else {
        assert(l < r);
        assert(arya_beats(days[r - 1]@));
        assert(arya_beats(days[r]@));
        assert(forall|t: int| l <= t && t <= r - 1 ==> arya_beats(#[trigger] days[t]@));
        lemma_segment_le_win_streak(days, l, r - 1);
        assert(win_streak_ending_at(days, r) == win_streak_ending_at(days, r - 1) + 1);
        assert((r - l + 1) <= win_streak_ending_at(days, r));
    }
}

proof fn lemma_win_streak_le_index(days: Seq<Vec<u8>>, idx: int)
    requires
        0 <= idx < days.len(),
    ensures
        win_streak_ending_at(days, idx) <= idx + 1,
    decreases idx + 1,
{
    if idx == 0 {
        assert(win_streak_ending_at(days, 0) == 0 || win_streak_ending_at(days, 0) == 1);
    } else {
        lemma_win_streak_le_index(days, idx - 1);
        if !arya_beats(days[idx]@) {
            assert(win_streak_ending_at(days, idx) == 0);
        } else if arya_beats(days[idx - 1]@) {
            assert(win_streak_ending_at(days, idx) == win_streak_ending_at(days, idx - 1) + 1);
            assert(win_streak_ending_at(days, idx - 1) <= idx);
            assert(win_streak_ending_at(days, idx) <= idx + 1);
        } else {
            assert(win_streak_ending_at(days, idx) == 1);
        }
    }
}

proof fn lemma_max_upto_ge_win_streak(days: Seq<Vec<u8>>, hi: int, j: int)
    requires
        0 <= j <= hi,
    ensures
        win_streak_ending_at(days, j) <= max_win_streak_upto(days, hi),
    decreases hi - j,
{
    if j == hi {
        assert(max_win_streak_upto(days, hi) >= win_streak_ending_at(days, hi));
    } else {
        lemma_max_upto_ge_win_streak(days, hi - 1, j);
        assert(max_win_streak_upto(days, hi) >= max_win_streak_upto(days, hi - 1));
    }
}

proof fn lemma_win_interval_of_streak_ending_at(days: Seq<Vec<u8>>, i: int)
    requires
        0 <= i < days.len(),
        arya_beats(days[i]@),
    ensures
        win_interval(days, i - win_streak_ending_at(days, i) + 1, i),
    decreases i + 1,
{
    let ws = win_streak_ending_at(days, i);
    let l = i - ws + 1;
    if i == 0 {
        assert(ws == 1);
        assert(l == 0);
        assert(win_interval(days, 0, 0));
    } else {
        if arya_beats(days[i - 1]@) {
            assert(ws == win_streak_ending_at(days, i - 1) + 1);
            assert(l == (i - 1) - win_streak_ending_at(days, i - 1) + 1);
            lemma_win_interval_of_streak_ending_at(days, i - 1);
            assert(win_interval(days, l, i - 1));
            assert(arya_beats(days[i]@));
            assert(win_interval(days, l, i));
        } else {
            assert(ws == 1);
            assert(l == i);
            assert(win_interval(days, i, i));
        }
    }
}

proof fn witness_end_for_max(days: Seq<Vec<u8>>, hi: int) -> (j: int)
    requires
        0 <= hi < days.len(),
    ensures
        0 <= j <= hi,
        win_streak_ending_at(days, j) == max_win_streak_upto(days, hi),
    decreases hi,
{
    if hi == 0 {
        reveal_with_fuel(max_win_streak_upto, 3);
        reveal_with_fuel(win_streak_ending_at, 3);
        assert(win_streak_ending_at(days, 0) == 0 || win_streak_ending_at(days, 0) == 1);
        assert(max_win_streak_upto(days, 0) == win_streak_ending_at(days, 0));
        0
    } else {
        let e = win_streak_ending_at(days, hi);
        let pm = max_win_streak_upto(days, hi - 1);
        if e > pm {
            assert(max_win_streak_upto(days, hi) == e);
            assert(win_streak_ending_at(days, hi) == max_win_streak_upto(days, hi));
            hi
        } else {
            let j0 = witness_end_for_max(days, hi - 1);
            j0
        }
    }
}

pub struct Solution;

impl Solution {
    fn is_win_row(row: &Vec<u8>) -> bool
        requires
            row.len() <= 100,
            forall|j: int| 0 <= j && j < row.len() ==> row[j] == 48u8 || row[j] == 49u8,
        returns
            arya_beats(row@),
    {
        let n = row.len();
        let mut j = 0usize;
        let mut found = false;
        while j < n
            invariant
                n == row.len(),
                j <= n,
                found == (exists|k: int| 0 <= k && k < j && #[trigger] row[k] == 48u8),
            decreases n - j,
        {
            proof {
                assert(j < row.len());
            }
            if row[j] == 48u8 {
                found = true;
            }
            j = j + 1;
        }
        proof {
            if n >= 1 {
                lemma_exists_zero_iff_beats(row@);
            } else {
                assert(row@.len() == 0);
                assert(!arya_beats(row@));
                assert(!found);
            }
        }
        found
    }

    pub fn max_consecutive_winning_days(n: usize, d: usize, days: &Vec<Vec<u8>>) -> (result: usize)
        requires
            1 <= n && n <= 100,
            1 <= d && d <= 100,
            days.len() == d,
            forall|i: int|
                0 <= i && i < d ==> #[trigger] days@[i].len() == n,
            forall|i: int, j: int|
                0 <= i && i < d && 0 <= j && j < n
                    ==> (#[trigger] days@[i]@[j] == 48u8 || #[trigger] days@[i]@[j] == 49u8),
        ensures
            result as int <= d as int,
            result as int == max_win_streak_upto(days@, d as int - 1),
            (result as int == 0) || (exists|l: int, r: int|
                0 <= l && l <= r && r < d as int && win_interval(days@, l, r) && r - l + 1 == result as int),
            forall|l: int, r: int|
                0 <= l && l <= r && r < d as int && win_interval(days@, l, r) ==> r - l + 1 <= result as int,
    {
        let _ = n;
        let mut best = 0usize;
        let mut cur = 0usize;
        let mut i = 0usize;
        proof {
            reveal_with_fuel(win_streak_ending_at, 5);
            reveal_with_fuel(max_win_streak_upto, 5);
            assert(win_streak_ending_at(days@, -1) == 0);
            assert(max_win_streak_upto(days@, -1) == 0);
            assert(cur as int == win_streak_ending_at(days@, i as int - 1));
            assert(best as int == max_win_streak_upto(days@, i as int - 1));
        }
        while i < d
            invariant
                1 <= n && n <= 100,
                1 <= d && d <= 100,
                days.len() == d,
                forall|ii: int|
                    0 <= ii && ii < d ==> #[trigger] days@[ii].len() == n,
                forall|ii: int, jj: int|
                    0 <= ii && ii < d && 0 <= jj && jj < n
                        ==> (#[trigger] days@[ii]@[jj] == 48u8 || #[trigger] days@[ii]@[jj] == 49u8),
                0 <= i && i <= d,
                cur as int == win_streak_ending_at(days@, i as int - 1),
                best as int == max_win_streak_upto(days@, i as int - 1),
            decreases d - i,
        {
            proof {
                if i > 0 {
                    lemma_win_streak_le_index(days@, i as int - 1);
                    assert((cur as int) + 1 <= d as int);
                }
            }
            if Solution::is_win_row(&days[i]) {
                proof {
                    assert(arya_beats(days@[i as int]@));
                }
                cur = cur + 1;
                proof {
                    reveal_with_fuel(win_streak_ending_at, 5);
                    if i == 0 {
                        assert(win_streak_ending_at(days@, 0) == 1);
                        assert(cur as int == win_streak_ending_at(days@, i as int));
                    } else {
                        assert(arya_beats(days@[i as int]@));
                        if arya_beats(days@[(i - 1) as int]@) {
                            assert(win_streak_ending_at(days@, i as int) == win_streak_ending_at(days@, (i - 1) as int) + 1);
                        } else {
                            assert(win_streak_ending_at(days@, i as int) == 1);
                        }
                        assert(cur as int == win_streak_ending_at(days@, i as int));
                    }
                }
            } else {
                proof {
                    assert(!arya_beats(days@[i as int]@));
                    reveal_with_fuel(win_streak_ending_at, 5);
                    assert(win_streak_ending_at(days@, i as int) == 0);
                }
                cur = 0;
                proof {
                    assert(cur as int == win_streak_ending_at(days@, i as int));
                }
            }
            proof {
                reveal_with_fuel(win_streak_ending_at, 5);
            }
            assert(cur as int == win_streak_ending_at(days@, i as int));
            let ghost prev_best = best;
            if cur > best {
                best = cur;
            } else {
            }
            proof {
                reveal_with_fuel(max_win_streak_upto, 5);
                assert(cur as int == win_streak_ending_at(days@, i as int));
                assert(
                    max_win_streak_upto(days@, i as int)
                        == if win_streak_ending_at(days@, i as int)
                            > max_win_streak_upto(days@, i as int - 1)
                        {
                            win_streak_ending_at(days@, i as int)
                        } else {
                            max_win_streak_upto(days@, i as int - 1)
                        }
                );
                if cur as int > prev_best as int {
                    assert(best as int == cur as int);
                } else {
                    assert(best as int == prev_best as int);
                }
            }
            assert(best as int == max_win_streak_upto(days@, i as int));
            i = i + 1;
        }
        proof {
            assert(i == d);
            assert(best as int == max_win_streak_upto(days@, d as int - 1));
            assert forall|l: int, r: int|
                (0 <= l && l <= r && r < d as int && win_interval(days@, l, r))
                    implies (r - l + 1) <= best as int by {
                assert forall|l: int, r: int|
                    (0 <= l && l <= r && r < d as int && win_interval(days@, l, r))
                        implies (r - l + 1) <= best as int by {
                    if 0 <= l && l <= r && r < d as int && win_interval(days@, l, r) {
                        lemma_segment_le_win_streak(days@, l, r);
                        lemma_max_upto_ge_win_streak(days@, d as int - 1, r);
                    }
                };
            };
            if best as int > 0 {
                let jm = witness_end_for_max(days@, d as int - 1);
                let rl = win_streak_ending_at(days@, jm);
                let lw = jm - rl + 1;
                lemma_win_streak_le_index(days@, jm);
                assert(rl <= jm + 1);
                assert(lw >= 0);
                assert(lw <= jm);
                assert(jm < d as int);
                lemma_win_interval_of_streak_ending_at(days@, jm);
                assert(win_interval(days@, lw, jm));
                assert(jm - lw + 1 == rl);
                assert(rl == max_win_streak_upto(days@, d as int - 1));
                assert(rl == best as int);
                assert(exists|l: int, r: int|
                    0 <= l && l <= r && r < d as int && win_interval(days@, l, r) && r - l + 1 == best as int);
            }
            assert(best as int <= d as int);
        }
        best
    }
}

}
