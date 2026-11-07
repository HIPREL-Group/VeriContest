use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_count(a: Seq<i32>, i: int, v: int) -> int
    decreases i,
{
    if i <= 0 {
        0int
    } else {
        spec_prefix_count(a, i - 1, v) + if a[i - 1] as int == v { 1int } else { 0int }
    }
}

pub open spec fn spec_orbit_contrib(k: int, c: int) -> int {
    if k <= 0 {
        0int
    } else if k < c {
        k
    } else {
        c
    }
}

pub open spec fn spec_sum_min_cost(a: Seq<i32>, c: int, vmax: int) -> int
    decreases vmax,
{
    if vmax <= 0 {
        0int
    } else {
        let k = spec_prefix_count(a, a.len() as int, vmax);
        spec_orbit_contrib(k, c) + spec_sum_min_cost(a, c, vmax - 1)
    }
}

proof fn lemma_i32_lt_implies_int_lt(x: i32, y: i32)
    requires
        x < y,
    ensures
        (x as int) < (y as int),
{
}

proof fn lemma_i32_ge_implies_int_ge(x: i32, y: i32)
    requires
        x >= y,
    ensures
        (x as int) >= (y as int),
{
}

proof fn lemma_orbit_contrib_le_c(k: int, c: int)
    requires
        1 <= c,
    ensures
        spec_orbit_contrib(k, c) <= c,
{
    if k <= 0 {
    } else if k < c {
        assert(spec_orbit_contrib(k, c) == k);
        assert(k < c);
    } else {
        assert(spec_orbit_contrib(k, c) == c);
    }
}

proof fn lemma_spec_prefix_count_nonneg(a: Seq<i32>, i: int, v: int)
    requires
        0 <= i <= a.len(),
    ensures
        spec_prefix_count(a, i, v) >= 0,
    decreases i,
{
    if i <= 0 {
    } else {
        lemma_spec_prefix_count_nonneg(a, i - 1, v);
    }
}

proof fn lemma_sum_step(a: Seq<i32>, c: int, v: int, n: int)
    requires
        1 <= v <= 100,
        n == a.len(),
        0 <= n <= 100,
    ensures
        spec_sum_min_cost(a, c, v) == spec_orbit_contrib(spec_prefix_count(a, n, v), c)
            + spec_sum_min_cost(a, c, v - 1),
{
    assert(spec_sum_min_cost(a, c, v) == ({
        let k = spec_prefix_count(a, a.len() as int, v);
        spec_orbit_contrib(k, c) + spec_sum_min_cost(a, c, v - 1)
    }));
    assert(spec_prefix_count(a, a.len() as int, v) == spec_prefix_count(a, n, v));
}

proof fn lemma_count_le_i(a: Seq<i32>, i: int, v: int)
    requires
        0 <= i <= a.len(),
    ensures
        spec_prefix_count(a, i, v) <= i,
    decreases i,
{
    if i <= 0 {
    } else {
        lemma_count_le_i(a, i - 1, v);
        assert(spec_prefix_count(a, i, v) <= spec_prefix_count(a, i - 1, v) + 1);
        assert(spec_prefix_count(a, i, v) <= i);
    }
}

proof fn lemma_prefix_other(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < 101,
        a[i] as int != j,
    ensures
        spec_prefix_count(a, i + 1, j) == spec_prefix_count(a, i, j),
{
}

proof fn lemma_prefix_hit(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        a[i] as int == j,
    ensures
        spec_prefix_count(a, i + 1, j) == spec_prefix_count(a, i, j) + 1,
{
}

impl Solution {
    pub fn min_destroy_cost(orbits: Vec<i32>, c: i32) -> (res: i32)
        requires
            1 <= orbits.len() <= 100,
            1 <= c <= 100,
            forall|i: int| 0 <= i < orbits.len() ==> 1 <= #[trigger] orbits@[i] <= 100,
        ensures
            res as int == spec_sum_min_cost(orbits@, c as int, 100),
    {
        let n = orbits.len();
        let ghost ni = n as int;
        proof {
            assert(ni == orbits@.len());
            assert(1 <= ni <= 100);
        }
        let mut cnt: Vec<i32> = Vec::new();
        let mut t = 0usize;
        while t < 101
            invariant
                t <= 101,
                cnt.len() == t,
                forall|j: int|
                    0 <= j < t as int ==> #[trigger] cnt@[j] == 0,
            decreases 101 - t,
        {
            cnt.push(0);
            t = t + 1;
        }
        let mut i = 0usize;
        while i < n
            invariant
                n == orbits.len(),
                ni == orbits@.len(),
                1 <= ni <= 100,
                i <= n,
                cnt.len() == 101,
                forall|k: int|
                    0 <= k < ni ==> 1 <= #[trigger] orbits@[k] <= 100,
                forall|j: int|
                    0 <= j < 101 ==> #[trigger] cnt@[j] == spec_prefix_count(orbits@, i as int, j),
            decreases n - i,
        {
            proof {
                assert(i < orbits.len());
                assert((i as int) < ni);
                assert(0 <= (i as int) && (i as int) < orbits.len());
                assert(1 <= orbits@[i as int] <= 100);
            }
            let x = orbits[i] as usize;
            proof {
                assert(x >= 1);
                assert(x <= 100);
                assert(x < cnt.len());
            }
            let prev = cnt[x];
            let ghost i0 = i as int;
            proof {
                assert(i0 < orbits@.len());
                assert(1 <= orbits@[i0] <= 100);
                assert(orbits@[i0] as int == x as int);
                assert(prev == spec_prefix_count(orbits@, i0, x as int));
                assert(i0 < ni);
                lemma_count_le_i(orbits@, i0, x as int);
                assert(prev <= i0);
                assert(prev < ni);
                assert(prev + 1 <= 101);
                assert(-2147483648 <= prev + 1 < 2147483648);
            }
            let ghost cnt0 = cnt@;
            cnt.set(x, prev + 1);
            proof {
                assert forall|j: int|
                    0 <= j < 101 implies cnt@[j] == spec_prefix_count(orbits@, i0 + 1, j)
                by {
                    if 0 <= j && j < 101 {
                        if j == x as int {
                            assert(orbits@[i0] as int == j);
                            lemma_prefix_hit(orbits@, i0, j);
                            assert(cnt@[j] == prev + 1);
                            assert(spec_prefix_count(orbits@, i0 + 1, j) == prev + 1);
                        } else {
                            assert(j != x as int);
                            assert(orbits@[i0] as int == x as int);
                            assert(orbits@[i0] as int != j);
                            lemma_prefix_other(orbits@, i0, j);
                            assert(cnt@[j] == cnt0[j]);
                            assert(cnt0[j] == spec_prefix_count(orbits@, i0, j));
                            assert(cnt@[j] == spec_prefix_count(orbits@, i0 + 1, j));
                        }
                    }
                };
            }
            i = i + 1;
        }
        let mut ans = 0i32;
        let mut v = 1usize;
        while v <= 100
            invariant
                n == orbits.len(),
                ni == orbits@.len(),
                1 <= ni <= 100,
                1 <= c <= 100,
                1 <= v <= 101,
                ans as int == spec_sum_min_cost(orbits@, c as int, (v - 1) as int),
                ans as int <= (v - 1) as int * 100,
                cnt.len() == 101,
                forall|j: int|
                    0 <= j < 101 ==> #[trigger] cnt@[j] == spec_prefix_count(orbits@, ni, j),
            decreases 101 - v,
        {
            proof {
                assert(v < cnt.len());
            }
            let k = cnt[v];
            let add = if k < c {
                k
            } else {
                c
            };
            proof {
                assert(k == spec_prefix_count(orbits@, ni, v as int));
                lemma_count_le_i(orbits@, ni, v as int);
                lemma_spec_prefix_count_nonneg(orbits@, ni, v as int);
                assert(0 <= k && k <= ni);
                lemma_sum_step(orbits@, c as int, v as int, ni);
                if k < c {
                    assert(add == k);
                    lemma_i32_lt_implies_int_lt(k, c);
                    assert((k as int) < c as int);
                    assert(spec_orbit_contrib(k as int, c as int) == k as int);
                } else {
                    assert(!(k < c));
                    assert(add == c);
                    assert(c >= 1);
                    assert(k >= c);
                    assert(k >= 1);
                    lemma_i32_ge_implies_int_ge(k, c);
                    assert((k as int) >= c as int);
                    assert(spec_orbit_contrib(k as int, c as int) == c as int) by {
                        let kk = k as int;
                        let cc = c as int;
                        assert(kk >= 1);
                        assert(kk >= cc);
                        assert(!(kk < cc));
                    };
                }
                assert(add as int == spec_orbit_contrib(k as int, c as int));
                assert(ans as int + add as int == spec_sum_min_cost(orbits@, c as int, v as int));
                assert((v as int) <= 100);
                assert(add <= 100);
                assert(ans as int <= ((v - 1) as int) * 100);
                assert(ans as int + add as int <= (v as int) * 100);
                assert((v as int) * 100 <= 100 * 100);
                assert(ans as int + add as int <= 100 * 100);
                assert((ans as int) + (add as int) <= 100 * 100);
            }
            ans = ans + add;
            v = v + 1;
        }
        proof {
            assert(v == 101);
            assert(ans as int == spec_sum_min_cost(orbits@, c as int, 100));
            assert forall|vv: int| 1 <= vv <= 100 implies #[trigger] spec_orbit_contrib(
                spec_prefix_count(orbits@, ni, vv),
                c as int,
            ) <= c as int by {
                lemma_orbit_contrib_le_c(spec_prefix_count(orbits@, ni, vv), c as int);
            };
        }
        ans
    }
}

}
