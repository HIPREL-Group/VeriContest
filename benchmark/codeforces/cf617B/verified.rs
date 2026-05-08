use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_nuts_range(a: Seq<i32>, lo: int, hi: int) -> int
    recommends
        0 <= lo && lo <= hi && hi <= a.len(),
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        (if (a[lo] as int) == 1 { 1int } else { 0int }) + count_nuts_range(a, lo + 1, hi)
    }
}

pub open spec fn count_nuts(a: Seq<i32>) -> int {
    count_nuts_range(a, 0, a.len() as int)
}

pub open spec fn last_nut_strictly_before(a: Seq<i32>, i: int) -> int
    recommends
        0 <= i && i <= a.len(),
    decreases i,
{
    if i <= 0 {
        -1
    } else if (a[i - 1] as int) == 1 {
        i - 1
    } else {
        last_nut_strictly_before(a, i - 1)
    }
}

pub open spec fn gap_product_prefix(a: Seq<i32>, end: int) -> int
    recommends
        0 <= end && end <= a.len(),
    decreases end,
{
    if end <= 0 {
        1
    } else if (a[end - 1] as int) == 0 {
        gap_product_prefix(a, end - 1)
    } else {
        let c = count_nuts_range(a, 0, end - 1);
        if c == 0 {
            1
        } else {
            let lastb = last_nut_strictly_before(a, end - 1);
            gap_product_prefix(a, end - 1) * ((end - 1) - lastb)
        }
    }
}

pub open spec fn chocolate_ways_spec(a: Seq<i32>) -> int {
    let k = count_nuts(a);
    if k == 0 {
        0
    } else if k == 1 {
        1
    } else {
        gap_product_prefix(a, a.len() as int)
    }
}

pub open spec fn pow2(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 } else { 2 * pow2(n - 1) }
}

proof fn lemma_pow2_pos(n: int)
    ensures pow2(n) >= 1,
    decreases n,
{
    if n <= 0 {} else { lemma_pow2_pos(n - 1); }
}

proof fn lemma_pow2_mono(a: int, b: int)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b - a,
{
    if a == b {
    } else {
        lemma_pow2_mono(a, b - 1);
        lemma_pow2_pos(b - 1);
    }
}

proof fn lemma_pow2_sum(a: int, b: int)
    requires a >= 0, b >= 0,
    ensures pow2(a) * pow2(b) == pow2(a + b),
    decreases a,
{
    if a == 0 {
    } else {
        lemma_pow2_sum(a - 1, b);
        assert(pow2(a) == 2 * pow2(a - 1));
        assert(pow2(a) * pow2(b) == 2 * pow2(a - 1) * pow2(b)) by (nonlinear_arith)
            requires
                pow2(a) == 2 * pow2(a - 1),
            ;
        assert(pow2(a - 1) * pow2(b) == pow2(a - 1 + b));
        assert(2 * pow2(a - 1) * pow2(b) == 2 * pow2(a - 1 + b)) by (nonlinear_arith)
            requires
                pow2(a - 1) * pow2(b) == pow2(a - 1 + b),
            ;
        assert(2 * pow2(a - 1 + b) == pow2(a + b));
    }
}

proof fn lemma_g_le_pow2(g: int)
    requires g >= 1,
    ensures g <= pow2(g),
    decreases g,
{
    if g == 1 {
        assert(pow2(1) == 2 * pow2(0));
        assert(pow2(0) == 1);
    } else {
        lemma_g_le_pow2(g - 1);
        assert(g - 1 <= pow2(g - 1));
        assert(pow2(g) == 2 * pow2(g - 1));
        assert(g <= 2 * pow2(g - 1)) by (nonlinear_arith)
            requires
                g >= 2,
                g - 1 <= pow2(g - 1),
                pow2(g - 1) >= 1,
            ;
    }
}

proof fn lemma_pow2_concrete(n: int)
    requires 0 <= n <= 10,
    ensures pow2(n) == if n == 0 { 1int } else if n == 1 { 2int } else if n == 2 { 4int }
        else if n == 3 { 8int } else if n == 4 { 16int } else if n == 5 { 32int }
        else if n == 6 { 64int } else if n == 7 { 128int } else if n == 8 { 256int }
        else if n == 9 { 512int } else { 1024int },
{
    reveal_with_fuel(pow2, 11);
}

proof fn lemma_pow2_99_bound()
    ensures
        pow2(99) < 340282366920938463463374607431768211456,
        pow2(99) < 170141183460469231731687303715884105728,
{
    lemma_pow2_sum(99, 7);
    lemma_pow2_concrete(7);
    assert(pow2(99) * 128 == pow2(106));
    lemma_pow2_sum(106, 22);
    lemma_pow2_concrete(10);
    lemma_pow2_sum(10, 10);
    assert(pow2(10) * pow2(10) == pow2(20));
    lemma_pow2_concrete(2);
    lemma_pow2_sum(20, 2);
    assert(pow2(20) * 4 == pow2(22));
    assert(pow2(106) * pow2(22) == pow2(128));
    lemma_pow2_pos(99);
    assert(pow2(99) >= 1);
    assert(128 >= 1) ;
    assert(pow2(99) <= pow2(106)) by {
        lemma_pow2_mono(99, 106);
    }
    assert(pow2(106) <= pow2(128)) by {
        lemma_pow2_mono(106, 128);
    }
    assert(pow2(128) <= 340282366920938463463374607431768211456) by {
        lemma_pow2_sum(64, 64);
        lemma_pow2_sum(32, 32);
        lemma_pow2_sum(16, 16);
        lemma_pow2_sum(8, 8);
        lemma_pow2_concrete(8);
        assert(pow2(8) == 256);
        assert(pow2(8) * pow2(8) == pow2(16)) by {
            lemma_pow2_sum(8, 8);
        }
        assert(256 * 256 == 65536) by (nonlinear_arith);
        assert(pow2(16) == 65536);
        assert(pow2(16) * pow2(16) == pow2(32)) by {
            lemma_pow2_sum(16, 16);
        }
        assert(65536int * 65536int == 4294967296int) by (nonlinear_arith);
        assert(pow2(32) == 4294967296);
        assert(pow2(32) * pow2(32) == pow2(64)) by {
            lemma_pow2_sum(32, 32);
        }
        assert(4294967296int * 4294967296int == 18446744073709551616int) by (nonlinear_arith);
        assert(pow2(64) == 18446744073709551616);
        assert(pow2(64) * pow2(64) == pow2(128)) by {
            lemma_pow2_sum(64, 64);
        }
        assert(18446744073709551616int * 18446744073709551616int == 340282366920938463463374607431768211456int) by (nonlinear_arith);
    }
    assert(pow2(99) < pow2(128)) by {
        lemma_pow2_mono(99, 127);
        lemma_pow2_pos(127);
        assert(pow2(128) == 2 * pow2(127));
        assert(pow2(99) <= pow2(127));
        assert(pow2(127) >= 1);
    }
    assert(pow2(99) < 340282366920938463463374607431768211456);
    assert(pow2(99) < 170141183460469231731687303715884105728) by {
        lemma_pow2_mono(99, 126);
        lemma_pow2_pos(126);
        assert(pow2(127) == 2 * pow2(126));
        assert(pow2(128) == 2 * pow2(127));
        assert(pow2(99) <= pow2(126));
        assert(pow2(127) <= 170141183460469231731687303715884105728);
    }
}

proof fn lemma_count_range_nonneg(a: Seq<i32>, lo: int, hi: int)
    requires
        0 <= lo && lo <= hi && hi <= a.len(),
        forall|j: int| 0 <= j < a.len() ==> (#[trigger] (a[j] as int) == 0 || (a[j] as int) == 1),
    ensures
        count_nuts_range(a, lo, hi) >= 0,
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        lemma_count_range_nonneg(a, lo + 1, hi);
    }
}

impl Solution {
    proof fn lemma_count_range_shift(a: Seq<i32>, lo: int, i: int)
        requires
            0 <= lo <= i && i < a.len(),
        ensures
            count_nuts_range(a, lo, i + 1) == count_nuts_range(a, lo, i) + if (a[i] as int) == 1 {
                1int
            } else {
                0int
            },
        decreases i - lo,
    {
        if lo == i {
            assert(count_nuts_range(a, lo, i) == 0);
            assert(count_nuts_range(a, lo, i + 1) == (if (a[lo] as int) == 1 { 1int } else { 0int }) + count_nuts_range(a, lo + 1, i + 1));
            assert(count_nuts_range(a, lo + 1, i + 1) == 0);
        } else {
            Self::lemma_count_range_shift(a, lo + 1, i);
        }
    }

    proof fn lemma_count_prefix_append(a: Seq<i32>, i: int)
        requires
            0 <= i < a.len(),
        ensures
            count_nuts_range(a, 0, i + 1) == count_nuts_range(a, 0, i) + if (a[i] as int) == 1 {
                1int
            } else {
                0int
            },
    {
        Self::lemma_count_range_shift(a, 0, i);
    }

    proof fn lemma_last_nut_before_bound(a: Seq<i32>, i: int)
        requires
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < a.len() ==> (#[trigger] (a[j] as int) == 0 || (a[j] as int) == 1),
        ensures
            last_nut_strictly_before(a, i) >= -1,
            last_nut_strictly_before(a, i) < i,
            count_nuts_range(a, 0, i) >= 1 ==> last_nut_strictly_before(a, i) >= 0,
        decreases i,
    {
        if i <= 0 {
        } else if (a[i - 1] as int) == 1 {
        } else {
            Self::lemma_last_nut_before_bound(a, i - 1);
            Self::lemma_count_prefix_append(a, i - 1);
        }
    }

    proof fn lemma_gap_product_prefix_pos(a: Seq<i32>, end: int)
        requires
            0 <= end <= a.len(),
            forall|j: int| 0 <= j < a.len() ==> (#[trigger] (a[j] as int) == 0 || (a[j] as int) == 1),
        ensures
            gap_product_prefix(a, end) >= 1,
        decreases end,
    {
        if end <= 0 {
        } else if (a[end - 1] as int) == 0 {
            Self::lemma_gap_product_prefix_pos(a, end - 1);
        } else {
            let c = count_nuts_range(a, 0, end - 1);
            if c == 0 {
            } else {
                Self::lemma_gap_product_prefix_pos(a, end - 1);
                lemma_count_range_nonneg(a, 0, end - 1);
                Self::lemma_last_nut_before_bound(a, end - 1);
                let lastb = last_nut_strictly_before(a, end - 1);
                let gap = (end - 1) - lastb;
                let prev = gap_product_prefix(a, end - 1);
                assert(prev >= 1 && gap >= 1);
                assert(prev * gap >= 1) by (nonlinear_arith)
                    requires prev >= 1, gap >= 1;
                assert(gap_product_prefix(a, end) == prev * gap);
            }
        }
    }

    #[verifier::loop_isolation(false)]
    pub fn chocolate_ways(n: usize, a: Vec<i32>) -> (result: i128)
        requires
            1 <= n <= 100,
            a.len() == n,
            forall|i: int| 0 <= i < n ==> (#[trigger] (a[i] as int) == 0 || (a[i] as int) == 1),
        ensures
            result as int == chocolate_ways_spec(a@),
    {
        let mut ans: u128 = 1;
        let mut prev: i64 = -1;
        let mut seen: usize = 0;
        let mut i: usize = 0;
        let ghost mut gap_sum: int = 0;
        let ghost mut first_nut: int = -1;
        while i < n
            invariant
                1 <= n <= 100,
                a.len() == n,
                forall|j: int| 0 <= j < n ==> (#[trigger] (a[j] as int) == 0 || (a[j] as int) == 1),
                i <= n,
                seen <= i,
                seen as int == count_nuts_range(a@, 0, i as int),
                ans as int == gap_product_prefix(a@, i as int),
                prev == -1 <==> seen == 0,
                seen >= 1 ==> 0 <= prev && (prev as int) < (i as int) && (a@[prev as int] as int) == 1,
                seen >= 1 ==> prev as int == last_nut_strictly_before(a@, i as int),
                1 <= ans,
                gap_sum >= 0,
                gap_sum <= 99,
                ans as int <= pow2(gap_sum),
                seen == 0 ==> gap_sum == 0 && first_nut == -1,
                seen == 1 ==> gap_sum == 0 && first_nut >= 0 && first_nut < i as int && first_nut == prev as int,
                seen >= 2 ==> first_nut >= 0 && gap_sum == (prev as int) - first_nut,
            decreases n - i,
        {
            proof {
                Self::lemma_count_prefix_append(a@, i as int);
            }
            if a[i] == 1 {
                if prev >= 0 {
                    let gap = i as u128 - prev as u128;
                    proof {
                        let g = gap as int;
                        assert(g == (i as int) - (prev as int));
                        assert(1 <= g && g <= 100);

                        lemma_count_range_nonneg(a@, 0, i as int);
                        assert(count_nuts_range(a@, 0, i as int) >= 1);
                        Self::lemma_last_nut_before_bound(a@, i as int);

                        lemma_g_le_pow2(g);
                        assert(g <= pow2(g));
                        assert(ans as int <= pow2(gap_sum));
                        assert(ans as int * g <= pow2(gap_sum) * pow2(g)) by (nonlinear_arith)
                            requires
                                ans as int >= 1,
                                ans as int <= pow2(gap_sum),
                                g >= 1,
                                g <= pow2(g),
                                pow2(gap_sum) >= 1,
                                pow2(g) >= 1,
                            ;
                        lemma_pow2_sum(gap_sum, g);
                        assert(pow2(gap_sum) * pow2(g) == pow2(gap_sum + g));
                        assert(gap_sum + g <= 99);
                        lemma_pow2_mono(gap_sum + g, 99);
                        lemma_pow2_99_bound();
                    }
                    ans = ans * gap;
                    proof {
                        let old_prev = prev as int;
                        gap_sum = gap_sum + (i as int) - old_prev;
                        assert(seen >= 1);
                        if seen == 1 {
                            assert(gap_sum == (i as int) - first_nut);
                        } else {
                            assert(gap_sum == old_prev - first_nut + (i as int) - old_prev);
                        }
                    }
                } else {
                    proof {
                        assert(count_nuts_range(a@, 0, i as int) == 0);
                        first_nut = i as int;
                    }
                }
                prev = i as i64;
                seen = seen + 1;
                proof {
                    Self::lemma_gap_product_prefix_pos(a@, (i + 1) as int);
                }
            } else {
            }
            i = i + 1;
        }
        assert(seen as int == count_nuts(a@));
        assert((ans as int) == gap_product_prefix(a@, a.len() as int));
        if seen == 0 {
            0
        } else if seen == 1 {
            1
        } else {
            proof {
                lemma_pow2_mono(gap_sum, 99);
                assert(pow2(gap_sum) <= pow2(99));
                assert(ans as int <= pow2(gap_sum));
                assert(ans as int <= pow2(99));
                lemma_pow2_99_bound();
            }
            ans as i128
        }
    }
}

}
