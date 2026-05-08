use vstd::prelude::*;
use vstd::arithmetic::div_mod::group_mod_properties;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_last_digit_of_multiple(k: int, m: int) -> int {
    (k * m) % 10
}

pub open spec fn spec_cycle_digit_sum(m: int) -> int {
    spec_last_digit_of_multiple(1, m) + spec_last_digit_of_multiple(2, m)
        + spec_last_digit_of_multiple(3, m) + spec_last_digit_of_multiple(4, m)
        + spec_last_digit_of_multiple(5, m) + spec_last_digit_of_multiple(6, m)
        + spec_last_digit_of_multiple(7, m) + spec_last_digit_of_multiple(8, m)
        + spec_last_digit_of_multiple(9, m) + spec_last_digit_of_multiple(10, m)
}

pub open spec fn spec_prefix_digit_sum(rem: int, m: int) -> int
    decreases rem
{
    if rem <= 0 {
        0
    } else {
        spec_prefix_digit_sum(rem - 1, m) + spec_last_digit_of_multiple(rem, m)
    }
}

pub open spec fn spec_book_reading_sum(n: int, m: int) -> int
    recommends
        n >= 1,
        m >= 1,
{
    let t = n / m;
    (t / 10) * spec_cycle_digit_sum(m) + spec_prefix_digit_sum(t % 10, m)
}

proof fn lemma_last_digit_in_0_9(k: int, mm: int)
    requires
        mm > 0,
    ensures
        0 <= spec_last_digit_of_multiple(k, mm) <= 9,
{
    assert(spec_last_digit_of_multiple(k, mm) == (k * mm) % 10);
    broadcast use group_mod_properties;
    assert(0 <= (k * mm) % 10 < 10);
}

proof fn lemma_prefix_sum_le_9_times_i(i: int, mm: int)
    requires
        1 <= i <= 10,
        1 <= mm,
    ensures
        spec_prefix_digit_sum(i, mm) <= 9 * i,
    decreases i,
{
    if i <= 1 {
        assert(spec_prefix_digit_sum(1, mm) == spec_last_digit_of_multiple(1, mm));
        lemma_last_digit_in_0_9(1, mm);
        assert(spec_prefix_digit_sum(1, mm) <= 9);
        assert(9 * 1 == 9);
    } else {
        lemma_prefix_sum_le_9_times_i(i - 1, mm);
        assert(spec_prefix_digit_sum(i, mm) == spec_prefix_digit_sum(i - 1, mm) + spec_last_digit_of_multiple(i, mm));
        lemma_last_digit_in_0_9(i, mm);
        assert(spec_prefix_digit_sum(i - 1, mm) + spec_last_digit_of_multiple(i, mm) <= 9 * (i - 1) + 9);
        assert(9 * (i - 1) + 9 == 9 * i) by (nonlinear_arith)
            requires
                1 <= i <= 10;
    }
}

proof fn lemma_mod10_mul_matches(i: int, m: int)
    requires
        1 <= i <= 10,
        1 <= m,
    ensures
        ((i % 10) * (m % 10)) % 10 == spec_last_digit_of_multiple(i, m),
{
    assert(spec_last_digit_of_multiple(i, m) == (i * m) % 10);
    assert((i * m) % 10 == ((i % 10) * (m % 10)) % 10) by (nonlinear_arith)
        requires
            1 <= i <= 10,
            1 <= m;
}

proof fn lemma_periodic_last_digit(k: int, m: int)
    requires
        1 <= k <= 10,
        1 <= m,
    ensures
        spec_last_digit_of_multiple(k + 10, m) == spec_last_digit_of_multiple(k, m),
{
    assert(spec_last_digit_of_multiple(k + 10, m) == ((k + 10) * m) % 10);
    assert(((k + 10) * m) == k * m + 10 * m) by (nonlinear_arith)
        requires
            1 <= k <= 10,
            1 <= m;
    assert(((k * m + 10 * m) % 10) == (k * m) % 10) by (nonlinear_arith)
        requires
            1 <= k <= 10,
            1 <= m;
    assert(spec_last_digit_of_multiple(k, m) == (k * m) % 10);
}

proof fn lemma_prefix_10_is_cycle(m: int)
    requires
        1 <= m,
    ensures
        spec_prefix_digit_sum(10, m) == spec_cycle_digit_sum(m),
{
    assert(spec_prefix_digit_sum(10, m) == spec_prefix_digit_sum(9, m) + spec_last_digit_of_multiple(10, m));
    assert(spec_prefix_digit_sum(9, m) == spec_prefix_digit_sum(8, m) + spec_last_digit_of_multiple(9, m));
    assert(spec_prefix_digit_sum(8, m) == spec_prefix_digit_sum(7, m) + spec_last_digit_of_multiple(8, m));
    assert(spec_prefix_digit_sum(7, m) == spec_prefix_digit_sum(6, m) + spec_last_digit_of_multiple(7, m));
    assert(spec_prefix_digit_sum(6, m) == spec_prefix_digit_sum(5, m) + spec_last_digit_of_multiple(6, m));
    assert(spec_prefix_digit_sum(5, m) == spec_prefix_digit_sum(4, m) + spec_last_digit_of_multiple(5, m));
    assert(spec_prefix_digit_sum(4, m) == spec_prefix_digit_sum(3, m) + spec_last_digit_of_multiple(4, m));
    assert(spec_prefix_digit_sum(3, m) == spec_prefix_digit_sum(2, m) + spec_last_digit_of_multiple(3, m));
    assert(spec_prefix_digit_sum(2, m) == spec_prefix_digit_sum(1, m) + spec_last_digit_of_multiple(2, m));
    assert(spec_prefix_digit_sum(1, m) == spec_prefix_digit_sum(0, m) + spec_last_digit_of_multiple(1, m));
    assert(spec_prefix_digit_sum(0, m) == 0);
    assert(spec_cycle_digit_sum(m) == spec_last_digit_of_multiple(1, m) + spec_last_digit_of_multiple(2, m)
        + spec_last_digit_of_multiple(3, m) + spec_last_digit_of_multiple(4, m)
        + spec_last_digit_of_multiple(5, m) + spec_last_digit_of_multiple(6, m)
        + spec_last_digit_of_multiple(7, m) + spec_last_digit_of_multiple(8, m)
        + spec_last_digit_of_multiple(9, m) + spec_last_digit_of_multiple(10, m));
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn book_reading_digit_sum(n: u64, m: u64) -> (r: u64)
        requires
            1 <= n <= 10_000_000_000_000_000,
            1 <= m <= 10_000_000_000_000_000,
        ensures
            (r as int) == spec_book_reading_sum(n as int, m as int),
    {
        proof {
            assert(1 <= n <= 10_000_000_000_000_000);
            assert(1 <= m <= 10_000_000_000_000_000);
        }
        let t = n / m;
        proof {
            assert(n >= 1);
            assert(m >= 1);
        }
        let m10 = m % 10;
        let mut cycle_sum: u64 = 0;
        let mut i: u64 = 1;
        proof {
            assert((n as int) >= 1);
            assert((m as int) >= 1);
            assert((t as int) == (n as int) / (m as int));
        }
        while i <= 10
            invariant
                1 <= i <= 11,
                1 <= n <= 10_000_000_000_000_000,
                1 <= m <= 10_000_000_000_000_000,
                m10 == m % 10,
                t == n / m,
                cycle_sum <= 90,
                (cycle_sum as int) == spec_prefix_digit_sum((i - 1) as int, m as int),
            decreases
                11 - i,
        {
            proof {
                assert((i as int) >= 1 && (i as int) <= 10);
                assert((i as int) % 10 >= 0 && (i as int) % 10 <= 9);
                assert((m as int) % 10 >= 0 && (m as int) % 10 <= 9);
            }
            let imod32 = (i % 10) as u32;
            let m1032 = m10 as u32;
            proof {
                assert((imod32 as int) == (i as int) % 10);
                assert((m1032 as int) == (m as int) % 10);
                assert((imod32 as int) <= 9);
                assert((m1032 as int) <= 9);
                assert((imod32 as int) * (m1032 as int) <= 81) by (nonlinear_arith)
                    requires
                        (imod32 as int) <= 9,
                        (m1032 as int) <= 9;
            }
            let d = ((imod32 * m1032) % 10) as u64;
            proof {
                assert(1 <= i && i <= 10);
                assert(n >= 1 && m >= 1);
                assert(m <= 10_000_000_000_000_000);
                assert((imod32 as int) == (i as int) % 10);
                assert((m1032 as int) == (m as int) % 10);
                lemma_mod10_mul_matches(i as int, m as int);
                assert((d as int) == ((imod32 as int) * (m1032 as int)) % 10) by (nonlinear_arith)
                    requires
                        (imod32 as int) <= 9,
                        (m1032 as int) <= 9,
                        d == ((imod32 * m1032) % 10) as u64;
                assert((d as int) == spec_last_digit_of_multiple(i as int, m as int));
                assert(spec_prefix_digit_sum(i as int, m as int) == spec_prefix_digit_sum((i - 1) as int, m as int)
                    + spec_last_digit_of_multiple(i as int, m as int));
                assert((cycle_sum as int) + (d as int) == spec_prefix_digit_sum(i as int, m as int));
                assert((cycle_sum + d) as int == (cycle_sum as int) + (d as int));
                lemma_prefix_sum_le_9_times_i(i as int, m as int);
                assert(spec_prefix_digit_sum(i as int, m as int) <= 90);
                assert((cycle_sum + d) as int <= 90);
                assert(cycle_sum + d <= 90);
            }
            cycle_sum = cycle_sum + d;
            proof {
                assert((cycle_sum as int) == spec_prefix_digit_sum(i as int, m as int));
                assert(cycle_sum <= 90);
            }
            i = i + 1;
        }
        proof {
            assert(i == 11);
            assert((cycle_sum as int) == spec_prefix_digit_sum(10, m as int));
            lemma_prefix_10_is_cycle(m as int);
            assert((cycle_sum as int) == spec_cycle_digit_sum(m as int));
        }
        let full = t / 10;
        let rem = t % 10;
        let mut partial: u64 = 0;
        i = 1;
        while i <= rem
            invariant
                1 <= i <= rem + 1,
                1 <= n <= 10_000_000_000_000_000,
                1 <= m <= 10_000_000_000_000_000,
                m10 == m % 10,
                t == n / m,
                rem == t % 10,
                full == t / 10,
                (rem as int) <= 9,
                (partial as int) == spec_prefix_digit_sum((i - 1) as int, m as int),
            decreases
                rem + 1 - i,
        {
            proof {
                assert((i as int) >= 1 && (i as int) <= (rem as int));
                assert((i as int) <= 9);
                assert((i as int) % 10 >= 0 && (i as int) % 10 <= 9);
                assert((m as int) % 10 >= 0 && (m as int) % 10 <= 9);
            }
            let imod32 = (i % 10) as u32;
            let m1032 = m10 as u32;
            proof {
                assert((imod32 as int) == (i as int) % 10);
                assert((m1032 as int) == (m as int) % 10);
                assert((imod32 as int) * (m1032 as int) <= 81) by (nonlinear_arith)
                    requires
                        (imod32 as int) <= 9,
                        (m1032 as int) <= 9;
            }
            let d = ((imod32 * m1032) % 10) as u64;
            proof {
                assert(1 <= i && i <= rem);
                assert(i <= 9);
                assert(1 <= i && i <= 10);
                assert(n >= 1 && m >= 1);
                assert(m <= 10_000_000_000_000_000);
                lemma_mod10_mul_matches(i as int, m as int);
                assert((d as int) == ((imod32 as int) * (m1032 as int)) % 10) by (nonlinear_arith)
                    requires
                        (imod32 as int) <= 9,
                        (m1032 as int) <= 9,
                        d == ((imod32 * m1032) % 10) as u64;
                assert((d as int) == spec_last_digit_of_multiple(i as int, m as int));
                assert((partial as int) + (d as int) == spec_prefix_digit_sum(i as int, m as int));
                lemma_prefix_sum_le_9_times_i(i as int, m as int);
                assert((i as int) <= (rem as int));
                assert((rem as int) <= 9);
                assert(spec_prefix_digit_sum(i as int, m as int) <= 9 * (i as int));
                assert(9 * (i as int) <= 81) by (nonlinear_arith)
                    requires
                        (i as int) <= 9;
                assert(spec_prefix_digit_sum(i as int, m as int) <= 81);
                assert((partial + d) as int <= 81);
                assert(partial + d <= 81);
            }
            partial = partial + d;
            proof {
                assert((partial as int) == spec_prefix_digit_sum(i as int, m as int));
                lemma_prefix_sum_le_9_times_i(i as int, m as int);
                assert((partial as int) <= 9 * (i as int));
                assert((i as int) <= (rem as int));
                assert((partial as int) <= 81);
            }
            i = i + 1;
        }
        proof {
            assert((partial as int) == spec_prefix_digit_sum(rem as int, m as int));
            assert((full as int) == (t as int) / 10);
            assert((rem as int) == (t as int) % 10);
            assert((cycle_sum as int) == spec_cycle_digit_sum(m as int));
            assert(spec_book_reading_sum(n as int, m as int) == (t as int / 10) * spec_cycle_digit_sum(m as int)
                + spec_prefix_digit_sum((t as int) % 10, m as int));
            assert((full as int) * (cycle_sum as int) + (partial as int) == spec_book_reading_sum(n as int, m as int));
            if rem >= 1 {
                lemma_prefix_sum_le_9_times_i(rem as int, m as int);
                assert((rem as int) <= 9);
                assert(spec_prefix_digit_sum(rem as int, m as int) <= 81);
            } else {
                assert(rem == 0);
                assert(spec_prefix_digit_sum(0, m as int) == 0);
            }
            assert((partial as int) <= 81);
        }
        proof {
            assert((full as int) <= (t as int));
            assert((cycle_sum as int) <= 90);
            assert((partial as int) <= 81);
            assert((t as int) <= (n as int));
            assert((full as int) * (cycle_sum as int) <= (t as int) * 90) by (nonlinear_arith)
                requires
                    (full as int) <= (t as int),
                    (cycle_sum as int) <= 90,
                    (full as int) == (t as int) / 10;
            assert((full as int) * (cycle_sum as int) + (partial as int) <= (t as int) * 90 + 81) by (nonlinear_arith)
                requires
                    (full as int) * (cycle_sum as int) <= (t as int) * 90,
                    (partial as int) <= 81;
            assert((t as int) * 90 + 81 < 18446744073709551615) by (nonlinear_arith)
                requires
                    (t as int) <= 10_000_000_000_000_000;
            assert(full * cycle_sum + partial <= 18446744073709551614u64);
        }
        let res = full * cycle_sum + partial;
        proof {
            assert((res as int) == (full as int) * (cycle_sum as int) + (partial as int));
            assert((res as int) == spec_book_reading_sum(n as int, m as int));
            assert(exists|tt: int|
                #![trigger spec_prefix_digit_sum(tt % 10, m as int)]
                tt == (n / m) as int && (res as int)
                    == (tt / 10) * spec_cycle_digit_sum(m as int) + spec_prefix_digit_sum(tt % 10, m as int));
            assert forall|k: int| (1 <= k && k <= 10) implies spec_last_digit_of_multiple(k + 10, m as int)
                == #[trigger] spec_last_digit_of_multiple(k, m as int) by {
                assert(1 <= k && k <= 10);
                lemma_periodic_last_digit(k, m as int);
            };
        }
        res
    }
}

}
