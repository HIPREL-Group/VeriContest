use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_eq_prefix(a: Seq<i32>, i: int, v: i32) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        count_eq_prefix(a, i - 1, v) + (if a[i - 1] == v { 1int } else { 0int })
    }
}

pub open spec fn seq_sum_prefix(a: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        seq_sum_prefix(a, n - 1) + a[n - 1] as int
    }
}

pub open spec fn fair_division_possible(a: Seq<i32>, n: int) -> bool {
    let c1 = count_eq_prefix(a, n, 1);
    let c2 = count_eq_prefix(a, n, 2);
    let total = c1 + 2 * c2;
    total % 2 == 0
        && exists|m: int|
            0 <= m && m <= c2 && 0 <= #[trigger] (total / 2 - 2 * m) && total / 2 - 2 * m <= c1
}

proof fn lemma_count_eq_prefix_nonneg(a: Seq<i32>, i: int, v: i32)
    ensures
        0 <= count_eq_prefix(a, i, v),
    decreases i,
{
    if i <= 0 {
    } else {
        lemma_count_eq_prefix_nonneg(a, i - 1, v);
    }
}

proof fn lemma_count_eq_prefix_succ(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len(),
        a[i] == 1 || a[i] == 2,
    ensures
        count_eq_prefix(a, i + 1, 1) == count_eq_prefix(a, i, 1) + (if a[i] == 1 { 1int } else { 0int }),
        count_eq_prefix(a, i + 1, 2) == count_eq_prefix(a, i, 2) + (if a[i] == 2 { 1int } else { 0int }),
{
    assert(i + 1 > 0);
    if a[i] == 1 {
        assert(count_eq_prefix(a, i + 1, 1) == count_eq_prefix(a, i, 1) + 1);
        assert(count_eq_prefix(a, i + 1, 2) == count_eq_prefix(a, i, 2));
    } else {
        assert(a[i] == 2);
        assert(count_eq_prefix(a, i + 1, 1) == count_eq_prefix(a, i, 1));
        assert(count_eq_prefix(a, i + 1, 2) == count_eq_prefix(a, i, 2) + 1);
    }
}

proof fn lemma_sum_matches_counts(a: Seq<i32>, n: int)
    requires
        0 <= n <= a.len(),
        forall|j: int| 0 <= j && j < n ==> a[j] == 1 || a[j] == 2,
    ensures
        seq_sum_prefix(a, n) == count_eq_prefix(a, n, 1) + 2 * count_eq_prefix(a, n, 2),
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_count_eq_prefix_nonneg(a, n - 1, 1);
        lemma_count_eq_prefix_nonneg(a, n - 1, 2);
        lemma_sum_matches_counts(a, n - 1);
        assert(a[n - 1] == 1 || a[n - 1] == 2);
        if a[n - 1] == 1 {
            assert(seq_sum_prefix(a, n) == seq_sum_prefix(a, n - 1) + 1);
            assert(count_eq_prefix(a, n, 1) == count_eq_prefix(a, n - 1, 1) + 1);
            assert(count_eq_prefix(a, n, 2) == count_eq_prefix(a, n - 1, 2));
        } else {
            assert(a[n - 1] == 2);
            assert(seq_sum_prefix(a, n) == seq_sum_prefix(a, n - 1) + 2);
            assert(count_eq_prefix(a, n, 1) == count_eq_prefix(a, n - 1, 1));
            assert(count_eq_prefix(a, n, 2) == count_eq_prefix(a, n - 1, 2) + 1);
        }
    }
}

proof fn lemma_total_parity_from_c1(c1: i32, c2: i32, total: i32)
    requires
        total == c1 + 2 * c2,
    ensures
        (total % 2 == 0) == (c1 % 2 == 0),
{
    assert(2 * c2 == c2 * 2);
    assert((2 * c2) % 2 == 0);
    assert(total % 2 == (c1 + 2 * c2) % 2);
    assert((c1 + 2 * c2) % 2 == c1 % 2);
}

proof fn lemma_implies_not_fair_when_odd(a: Seq<i32>, n: int, c1i: int, c2i: int)
    requires
        0 <= n,
        c1i == count_eq_prefix(a, n, 1),
        c2i == count_eq_prefix(a, n, 2),
        (c1i + 2 * c2i) % 2 != 0,
    ensures
        !fair_division_possible(a, n),
{
    let c1 = count_eq_prefix(a, n, 1);
    let c2 = count_eq_prefix(a, n, 2);
    let total = c1 + 2 * c2;
    assert(c1i == c1 && c2i == c2);
    assert(total % 2 != 0);
    assert(!fair_division_possible(a, n));
}

proof fn lemma_exists_m_from_witness(c1: int, c2: int, half: int, m: int)
    requires
        0 <= m && m <= c2,
        0 <= half - 2 * m && half - 2 * m <= c1,
        2 * half == c1 + 2 * c2,
    ensures
        exists|mm: int|
            0 <= mm && mm <= c2 && 0 <= #[trigger] ((c1 + 2 * c2) / 2 - 2 * mm) && (c1 + 2 * c2) / 2 - 2 * mm <= c1,
{
    assert(half == (c1 + 2 * c2) / 2);
    assert((c1 + 2 * c2) / 2 - 2 * m == half - 2 * m);
    assert(exists|mm: int|
        0 <= mm && mm <= c2 && 0 <= #[trigger] ((c1 + 2 * c2) / 2 - 2 * mm) && (c1 + 2 * c2) / 2 - 2 * mm <= c1);
}

proof fn lemma_forall_m_fails_implies_no_exists(c1: int, c2: int, half: int)
    requires
        2 * half == c1 + 2 * c2,
        forall|m: int| #![trigger half - 2 * m]
            (0 <= m && m <= c2) ==> (!(0 <= half - 2 * m && half - 2 * m <= c1)),
    ensures
        !(exists|mm: int|
            0 <= mm && mm <= c2 && 0 <= #[trigger] ((c1 + 2 * c2) / 2 - 2 * mm) && (c1 + 2 * c2) / 2 - 2 * mm <= c1),
{
    assert(half == (c1 + 2 * c2) / 2);
    assert forall|mm: int| #![trigger (c1 + 2 * c2) / 2 - 2 * mm]
        !(0 <= mm && mm <= c2 && 0 <= (c1 + 2 * c2) / 2 - 2 * mm && (c1 + 2 * c2) / 2 - 2 * mm <= c1) by {
        if 0 <= mm && mm <= c2 && 0 <= (c1 + 2 * c2) / 2 - 2 * mm && (c1 + 2 * c2) / 2 - 2 * mm <= c1 {
            assert(0 <= half - 2 * mm && half - 2 * mm <= c1);
            assert(0 <= mm && mm <= c2);
            assert(!(0 <= half - 2 * mm && half - 2 * mm <= c1));
        }
    }
}

pub struct Solution;

impl Solution {
    pub fn fair_division(n: usize, a: Vec<i32>) -> (res: bool)
        requires
            1 <= n <= 100,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> (a@[i] == 1 || a@[i] == 2),
        ensures
            res == fair_division_possible(a@, n as int),
    {
        let mut c1: i32 = 0;
        let mut c2: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i && i <= n,
                a.len() == n,
                n <= 100,
                c1 as int == count_eq_prefix(a@, i as int, 1),
                c2 as int == count_eq_prefix(a@, i as int, 2),
                (c1 as int) + (c2 as int) == i as int,
                (c1 as int) <= i as int,
                (c2 as int) <= i as int,
                forall|j: int| 0 <= j && j < n ==> (a@[j] == 1 || a@[j] == 2),
            decreases n - i
        {
            proof {
                assert(a@[i as int] == 1 || a@[i as int] == 2);
                lemma_count_eq_prefix_succ(a@, i as int);
            }
            if a[i] == 1 {
                proof {
                    assert((c1 + 1) as int == count_eq_prefix(a@, (i + 1) as int, 1));
                    assert(c2 as int == count_eq_prefix(a@, (i + 1) as int, 2));
                }
                c1 = c1 + 1;
            } else {
                proof {
                    assert(c1 as int == count_eq_prefix(a@, (i + 1) as int, 1));
                    assert((c2 + 1) as int == count_eq_prefix(a@, (i + 1) as int, 2));
                }
                c2 = c2 + 1;
            }
            i = i + 1;
            proof {
                assert(c1 as int == count_eq_prefix(a@, i as int, 1));
                assert(c2 as int == count_eq_prefix(a@, i as int, 2));
                assert((c1 as int) + (c2 as int) == i as int);
            }
        }
        proof {
            assert(i == n);
            assert(c1 as int == count_eq_prefix(a@, n as int, 1));
            assert(c2 as int == count_eq_prefix(a@, n as int, 2));
            assert((c2 as int) <= n as int);
            lemma_sum_matches_counts(a@, n as int);
            assert(seq_sum_prefix(a@, n as int) == c1 as int + 2 * (c2 as int));
        }
        let total = c1 + 2 * c2;
        if total % 2 != 0 {
            proof {
                lemma_implies_not_fair_when_odd(a@, n as int, c1 as int, c2 as int);
                assert((c1 as int + 2 * (c2 as int)) % 2 != 0);
                assert(!fair_division_possible(a@, n as int));
            }
            return false;
        }
        let half = total / 2;
        proof {
            lemma_total_parity_from_c1(c1, c2, total);
            assert(2 * (half as int) == c1 as int + 2 * (c2 as int));
        }
        let mut m: i32 = 0;
        while m <= c2
            invariant
                a.len() == n,
                c1 as int == count_eq_prefix(a@, n as int, 1),
                c2 as int == count_eq_prefix(a@, n as int, 2),
                total == c1 + 2 * c2,
                total % 2 == 0,
                half == total / 2,
                2 * (half as int) == c1 as int + 2 * (c2 as int),
                c2 >= 0 && c2 <= 100,
                0 <= m && m <= c2 + 1 && m <= 101,
                forall|k: int|
                    (0 <= k && k < (m as int)) ==> !(0 <= #[trigger] (half as int - 2 * k) && half as int - 2 * k <= c1 as int),
            decreases 101 - m
        {
            proof {
                assert(m <= c2);
                assert(2 * m <= 200);
            }
            let n1 = half - 2 * m;
            if n1 >= 0 && n1 <= c1 {
                proof {
                    let c1i = c1 as int;
                    let c2i = c2 as int;
                    let halfi = half as int;
                    let mi = m as int;
                    assert(0 <= mi && mi <= c2i);
                    assert(0 <= halfi - 2 * mi && halfi - 2 * mi <= c1i);
                    assert(2 * halfi == c1i + 2 * c2i);
                    lemma_exists_m_from_witness(c1i, c2i, halfi, mi);
                    assert(fair_division_possible(a@, n as int));
                }
                return true;
            }
            proof {
                assert(forall|k: int|
                    (0 <= k && k < (m as int)) ==> !(0 <= #[trigger] (half as int - 2 * k) && half as int - 2 * k <= c1 as int));
                let k = m as int;
                assert(!(0 <= half as int - 2 * k && half as int - 2 * k <= c1 as int));
            }
            proof {
                assert(m <= 100);
                assert(m + 1 <= 101);
            }
            m = m + 1;
        }
        proof {
            let c1i = c1 as int;
            let c2i = c2 as int;
            let halfi = half as int;
            assert(m == c2 + 1);
            assert(forall|k: int|
                (0 <= k && k <= c2i) ==> !(0 <= #[trigger] (halfi - 2 * k) && halfi - 2 * k <= c1i));
            lemma_forall_m_fails_implies_no_exists(c1i, c2i, halfi);
            assert(!fair_division_possible(a@, n as int));
        }
        false
    }
}

}
