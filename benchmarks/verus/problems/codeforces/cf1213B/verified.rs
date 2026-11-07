use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_range(a: Seq<i32>, lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi < a.len(),
    decreases
        hi - lo,
{
    if lo < hi {
        let m = min_range(a, lo + 1, hi);
        if (a[lo] as int) < m {
            a[lo] as int
        } else {
            m
        }
    } else {
        a[lo] as int
    }
}

pub open spec fn has_smaller_to_right(a: Seq<i32>, i: int) -> bool {
    exists |j: int| i < j < a.len() && (#[trigger] a[j]) < (#[trigger] a[i])
}

pub open spec fn count_bad_recursive(a: Seq<i32>, start: int) -> int
    recommends
        0 <= start <= a.len(),
    decreases
        a.len() - start,
{
    if start >= a.len() {
        0
    } else {
        count_bad_recursive(a, start + 1) + if has_smaller_to_right(a, start) {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn count_bad_prices_spec(a: Seq<i32>) -> int {
    count_bad_recursive(a, 0)
}

proof fn lemma_min_range_member(a: Seq<i32>, lo: int, hi: int) -> (j: int)
    requires
        0 <= lo <= hi < a.len(),
    ensures
        lo <= j <= hi,
        a[j] as int == min_range(a, lo, hi),
    decreases
        hi - lo,
{
    if lo < hi {
        let m = min_range(a, lo + 1, hi);
        if (a[lo] as int) < m {
            lo
        } else {
            lemma_min_range_member(a, lo + 1, hi)
        }
    } else {
        lo
    }
}

proof fn lemma_min_le_all(a: Seq<i32>, lo: int, hi: int, k: int)
    requires
        0 <= lo <= hi < a.len(),
        lo <= k <= hi,
    ensures
        min_range(a, lo, hi) <= a[k] as int,
    decreases
        hi - lo,
{
    if lo < hi {
        let m = min_range(a, lo + 1, hi);
        if (a[lo] as int) < m {
            assert(min_range(a, lo, hi) == a[lo] as int);
            if k == lo {
            } else {
                assert(lo < k);
                lemma_min_le_all(a, lo + 1, hi, k);
                assert(min_range(a, lo + 1, hi) <= a[k] as int);
                assert(m <= a[k] as int);
                assert((a[lo] as int) < m);
                assert((a[lo] as int) <= m);
                assert((a[lo] as int) <= a[k] as int);
            }
        } else {
            assert(min_range(a, lo, hi) == m);
            if k == lo {
                lemma_min_le_all(a, lo + 1, hi, lo + 1);
                assert(min_range(a, lo + 1, hi) <= a[lo + 1] as int);
                assert(m <= a[lo + 1] as int);
                assert(!((a[lo] as int) < m));
                assert((a[lo] as int) >= m);
            } else {
                lemma_min_le_all(a, lo + 1, hi, k);
            }
        }
    } else {
        assert(k == lo);
    }
}

proof fn lemma_exists_implies_min_lt(a: Seq<i32>, i: int, n1: int)
    requires
        n1 == a.len(),
        n1 >= 2,
        0 <= i < n1 - 1,
        has_smaller_to_right(a, i),
    ensures
        min_range(a, i + 1, n1 - 1) < (a[i] as int),
{
    assert(exists |j: int| i < j < n1 && a[j] < a[i]);
    let j = choose|j: int| i < j < n1 && a[j] < a[i];
    lemma_min_le_all(a, i + 1, n1 - 1, j);
    assert(min_range(a, i + 1, n1 - 1) <= a[j] as int);
    assert((a[j] as int) < (a[i] as int));
}

proof fn lemma_min_lt_implies_exists(a: Seq<i32>, i: int, n1: int)
    requires
        n1 == a.len(),
        n1 >= 2,
        0 <= i < n1 - 1,
        min_range(a, i + 1, n1 - 1) < (a[i] as int),
    ensures
        has_smaller_to_right(a, i),
{
    let j = lemma_min_range_member(a, i + 1, n1 - 1);
    assert(a[j] as int == min_range(a, i + 1, n1 - 1));
    assert((a[j] as int) < (a[i] as int));
    assert(i < j);
    assert(j < n1);
}

proof fn lemma_gt_min_iff_bad(a: Seq<i32>, i: int, n1: int)
    requires
        n1 == a.len(),
        n1 >= 2,
        0 <= i < n1 - 1,
    ensures
        (min_range(a, i + 1, n1 - 1) < (a[i] as int)) == has_smaller_to_right(a, i),
{
    if min_range(a, i + 1, n1 - 1) < (a[i] as int) {
        lemma_min_lt_implies_exists(a, i, n1);
    } else {
        assert forall |j: int| i < j < n1 implies (a[j] as int) >= (a[i] as int) by {
            lemma_min_le_all(a, i + 1, n1 - 1, j);
            assert(min_range(a, i + 1, n1 - 1) <= a[j] as int);
            assert(!(min_range(a, i + 1, n1 - 1) < (a[i] as int)));
            assert(a[j] as int >= min_range(a, i + 1, n1 - 1));
            assert((a[j] as int) >= (a[i] as int));
        };
        assert(!has_smaller_to_right(a, i));
    }
}

proof fn lemma_count_bad_step(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        count_bad_recursive(a, i) == count_bad_recursive(a, i + 1) + if has_smaller_to_right(a, i) {
            1int
        } else {
            0int
        },
{
}

proof fn lemma_count_bad_upper(a: Seq<i32>, k: int)
    requires
        0 <= k <= a.len(),
    ensures
        count_bad_recursive(a, k) <= a.len() - k,
    decreases
        a.len() - k,
{
    if k >= a.len() {
    } else {
        lemma_count_bad_upper(a, k + 1);
        assert(count_bad_recursive(a, k) <= 1 + (a.len() - (k + 1)));
        assert(1 + (a.len() - (k + 1)) == a.len() - k);
    }
}

proof fn lemma_no_smaller_last(a: Seq<i32>)
    requires
        a.len() >= 1,
    ensures
        !has_smaller_to_right(a, a.len() - 1),
{
    let last = a.len() - 1;
    assert forall |j: int| !((last < j && j < a.len()) && a[j] < a[last]) by {
        if last < j && j < a.len() {
            assert(j >= last + 1);
            assert(j < a.len());
            assert(last + 1 == a.len());
            assert(j >= a.len());
            assert(false);
        }
    };
}

proof fn lemma_count_suffix_zero(a: Seq<i32>, s: int)
    requires
        s == a.len(),
        s >= 0,
    ensures
        count_bad_recursive(a, s) == 0,
{
    assert(s >= a.len());
    assert(count_bad_recursive(a, s) == 0);
}

proof fn lemma_count_one_element(a: Seq<i32>)
    requires
        a.len() == 1,
    ensures
        count_bad_recursive(a, 0) == 0,
{
    lemma_no_smaller_last(a);
    assert(!has_smaller_to_right(a, 0));
    lemma_count_suffix_zero(a, 1int);
    assert(
        count_bad_recursive(a, 0) == count_bad_recursive(a, 1) + if has_smaller_to_right(a, 0) {
        1int
    } else {
        0int
    }
    );
}

proof fn lemma_count_from_penultimate_zero(a: Seq<i32>)
    requires
        a.len() >= 2,
    ensures
        count_bad_recursive(a, a.len() - 1) == 0,
{
    lemma_no_smaller_last(a);
    lemma_count_suffix_zero(a, a.len() as int);
    let last = a.len() - 1;
    let cr = count_bad_recursive(a, a.len() as int);
    assert(cr == 0);
    assert(
        count_bad_recursive(a, last)
            == cr + if has_smaller_to_right(a, last) {
            1int
        } else {
            0int
        }
    );
}

proof fn lemma_min_extend(a: Seq<i32>, i: int, n1: int)
    requires
        n1 == a.len(),
        n1 >= 2,
        0 <= i < n1 - 1,
    ensures
        min_range(a, i, n1 - 1)
            == if (a[i] as int) < min_range(a, i + 1, n1 - 1) {
                a[i] as int
            } else {
                min_range(a, i + 1, n1 - 1)
            },
{
}

impl Solution {
    #[verifier::loop_isolation(false)]
    pub fn count_bad_prices(a: Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() <= 150_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= (#[trigger] a[k]) <= 1_000_000,
        ensures
            result == count_bad_prices_spec(a@),
    {
        let n = a.len();
        if n <= 1 {
            proof {
                lemma_count_one_element(a@);
            }
            return 0;
        }
        let mut cnt: i32 = 0;
        let mut cur_min = a[n - 1];
        let mut i: usize = n - 2;
        proof {
            lemma_count_from_penultimate_zero(a@);
            assert(min_range(a@, (n - 1) as int, (n - 1) as int) == a@[(n - 1) as int] as int);
            assert(cur_min as int == min_range(a@, (i + 1) as int, (n - 1) as int));
            assert(count_bad_recursive(a@, (i + 1) as int) == 0);
        }
        loop
            invariant
                2 <= n <= 150_000,
                n == a.len(),
                forall |k: int| 0 <= k < n as int ==> 1 <= (#[trigger] a@[k]) <= 1_000_000,
                i <= n - 2,
                cur_min as int == min_range(a@, (i + 1) as int, (n - 1) as int),
                cnt as int == count_bad_recursive(a@, (i + 1) as int),
            decreases i,
        {
            proof {
                lemma_gt_min_iff_bad(a@, i as int, n as int);
            }
            if a[i] > cur_min {
                proof {
                    assert(min_range(a@, (i + 1) as int, (n - 1) as int) < (a@[i as int] as int));
                    assert(has_smaller_to_right(a@, i as int));
                    lemma_count_bad_step(a@, i as int);
                    let crp1 = count_bad_recursive(a@, (i + 1) as int);
                    assert(count_bad_recursive(a@, i as int) == crp1 + 1int);
                }
                proof {
                    lemma_count_bad_upper(a@, (i + 1) as int);
                    assert((cnt as int) + 1 <= a@.len() - (i as int));
                    assert((cnt as int) + 1 <= (n as int));
                    assert((cnt as int) + 1 <= 150_000);
                }
                cnt = cnt + 1;
                proof {
                    assert(cnt as int == count_bad_recursive(a@, i as int));
                }
            } else {
                proof {
                    assert(min_range(a@, (i + 1) as int, (n - 1) as int) >= (a@[i as int] as int));
                    assert(!has_smaller_to_right(a@, i as int));
                    lemma_count_bad_step(a@, i as int);
                    assert(
                        count_bad_recursive(a@, i as int) == count_bad_recursive(a@, (i + 1) as int)
                    );
                }
                proof {
                    assert(cnt as int == count_bad_recursive(a@, i as int));
                }
            }
            if a[i] < cur_min {
                cur_min = a[i];
            }
            proof {
                lemma_min_extend(a@, i as int, n as int);
                let old_m = min_range(a@, (i + 1) as int, (n - 1) as int);
                let ai = a@[i as int] as int;
                if ai < old_m {
                    assert(cur_min as int == ai);
                    assert(ai < old_m);
                    assert(cur_min as int == min_range(a@, i as int, (n - 1) as int));
                } else {
                    assert(cur_min as int == old_m);
                    assert(!(ai < old_m));
                    assert(cur_min as int == min_range(a@, i as int, (n - 1) as int));
                }
            }
            if i == 0 {
                proof {
                    assert(cnt as int == count_bad_recursive(a@, 0));
                }
                break;
            }
            i = i - 1;
            proof {
                assert(cur_min as int == min_range(a@, (i + 1) as int, (n - 1) as int));
                assert(cnt as int == count_bad_recursive(a@, (i + 1) as int));
            }
        }
        proof {
            assert(cnt as int == count_bad_recursive(a@, 0));
            assert(cnt as int == count_bad_prices_spec(a@));
        }
        cnt
    }
}

}
