use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_seq_sum(s: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= s.len(),
    decreases k as nat,
{
    if k <= 0 {
        0int
    } else {
        spec_seq_sum(s, k - 1) + (s[k - 1] as int)
    }
}

pub open spec fn spec_partial_sum(i: int, b: int, r: int) -> int
    recommends
        0 <= i,
        0 <= r,
{
    if i <= r {
        i * (b + 1)
    } else {
        r * (b + 1) + (i - r) * b
    }
}

pub open spec fn spec_seq_max(s: Seq<i32>, k: int) -> int
    recommends
        0 < k <= s.len(),
{
    s.take(k).map_values(|x| x as int).max()
}

pub open spec fn spec_seq_min(s: Seq<i32>, k: int) -> int
    recommends
        0 < k <= s.len(),
{
    s.take(k).map_values(|x| x as int).min()
}

pub open spec fn spec_valid_candy_split(s: Seq<i32>, n: int, m: int) -> bool {
    s.len() == m && spec_seq_sum(s, m) == n && forall|j: int|
        0 <= j < m ==> (#[trigger] s[j] as int) >= 1
}

pub open spec fn spec_int_ceil_div(n: int, m: int) -> int
    recommends
        0 < m,
{
    (n + m - 1) / m
}

pub open spec fn spec_tail_val(idx: int, b: int, r: int) -> i32
    recommends
        0 <= b <= 100,
{
    if idx < r {
        (b + 1) as i32
    } else {
        b as i32
    }
}

pub open spec fn spec_gift_seq(i: int, b: int, r: int) -> Seq<i32>
    recommends
        i >= 0,
        0 <= b <= 100,
    decreases i as nat,
{
    if i <= 0 {
        seq![]
    } else {
        spec_gift_seq(i - 1, b, r).push(spec_tail_val(i - 1, b, r))
    }
}

proof fn lemma_base_pos(n: i32, m: i32, b: i32)
    requires
        1 <= m,
        m <= n,
        n <= 100,
        b == n / m,
    ensures
        b >= 1,
        (b as int) <= 100,
{
    assert((n as int) / (m as int) >= 1) by (nonlinear_arith)
        requires
            1 <= (m as int) <= (n as int),
    ;
    assert((b as int) == (n as int) / (m as int));
    assert(b <= n);
    assert((b as int) <= (n as int));
    assert((n as int) <= 100);
}

proof fn lemma_rem_range(n: i32, m: i32, r: i32)
    requires
        1 <= m <= n <= 100,
        r == n % m,
    ensures
        0 <= r < m,
{
}

proof fn lemma_div_identity(n: i32, m: i32, b: i32, r: i32)
    requires
        1 <= m <= n <= 100,
        b == n / m,
        r == n % m,
    ensures
        (n as int) == (m as int) * (b as int) + (r as int),
{
    lemma_fundamental_div_mod(n as int, m as int);
    assert((n as int) == (n as int) / (m as int) * (m as int) + (n as int) % (m as int));
    assert((b as int) == (n as int) / (m as int));
    assert((r as int) == (n as int) % (m as int));
}

proof fn lemma_partial_total(m: int, b: int, r: int)
    requires
        m >= 1,
        0 <= r < m,
        0 <= b,
    ensures
        spec_partial_sum(m, b, r) == m * b + r,
{
    assert(!(m <= r));
    assert(spec_partial_sum(m, b, r) == r * (b + 1) + (m - r) * b);
    assert(r * (b + 1) + (m - r) * b == m * b + r) by (nonlinear_arith)
        requires
            0 <= r,
            0 <= m,
            0 <= b,
    {
    }
}

proof fn lemma_gift_seq_len(i: int, b: int, r: int)
    requires
        i >= 0,
    ensures
        spec_gift_seq(i, b, r).len() == i,
    decreases i as nat,
{
    if i > 0 {
        lemma_gift_seq_len(i - 1, b, r);
    }
}

proof fn lemma_gift_push(i: int, b: int, r: int, val: i32)
    requires
        i >= 0,
        val == spec_tail_val(i, b, r),
    ensures
        spec_gift_seq(i + 1, b, r) == spec_gift_seq(i, b, r).push(val),
    decreases i as nat,
{
    assert(spec_gift_seq(i + 1, b, r) == spec_gift_seq(i, b, r).push(spec_tail_val(i, b, r)));
}

proof fn lemma_sum_prefix_eq(s: Seq<i32>, t: Seq<i32>, k: int)
    requires
        0 <= k <= s.len(),
        0 <= k <= t.len(),
        forall|j: int|
            0 <= j < k ==> (#[trigger] s[j] as int) == t[j] as int,
    ensures
        spec_seq_sum(s, k) == spec_seq_sum(t, k),
    decreases k as nat,
{
    if k > 0 {
        lemma_sum_prefix_eq(s, t, k - 1);
    }
}

proof fn lemma_seq_sum_push(s: Seq<i32>, k: int, x: i32)
    requires
        k >= 0,
        k == s.len(),
    ensures
        spec_seq_sum(s.push(x), k + 1) == spec_seq_sum(s, k) + (x as int),
    decreases k as nat,
{
    reveal_with_fuel(spec_seq_sum, 200);
    let t = s.push(x);
    assert(k + 1 <= t.len());
    lemma_sum_prefix_eq(s, t, k);
    assert(spec_seq_sum(t, k) == spec_seq_sum(s, k));
    assert(spec_seq_sum(t, k + 1) == spec_seq_sum(t, k) + (t[k] as int));
    assert(t[k] == x);
}

proof fn lemma_partial_sum_step_lt_rem(ii: int, b: int, r: int)
    requires
        0 <= ii < r,
        0 <= r,
        0 <= b,
    ensures
        spec_partial_sum(ii + 1, b, r) == spec_partial_sum(ii, b, r) + (b + 1),
{
    assert(ii + 1 <= r);
    assert(spec_partial_sum(ii, b, r) == ii * (b + 1));
    assert(spec_partial_sum(ii + 1, b, r) == (ii + 1) * (b + 1));
    assert((ii + 1) * (b + 1) == ii * (b + 1) + (b + 1)) by (nonlinear_arith)
        requires
            0 <= ii,
            0 <= b,
    {
    }
}

proof fn lemma_partial_sum_step_ge_rem(ii: int, b: int, r: int)
    requires
        r <= ii,
        0 <= r,
        0 <= b,
    ensures
        spec_partial_sum(ii + 1, b, r) == spec_partial_sum(ii, b, r) + b,
{
    assert(ii + 1 > r);
    if ii <= r {
        assert(ii == r);
        assert(spec_partial_sum(ii, b, r) == r * (b + 1));
        assert(spec_partial_sum(ii + 1, b, r) == r * (b + 1) + (ii + 1 - r) * b);
        assert(ii + 1 - r == 1);
        assert(spec_partial_sum(ii + 1, b, r) == spec_partial_sum(ii, b, r) + b) by (nonlinear_arith)
            requires
                spec_partial_sum(ii, b, r) == r * (b + 1),
                spec_partial_sum(ii + 1, b, r) == r * (b + 1) + (ii + 1 - r) * b,
                ii == r,
                ii + 1 - r == 1,
        {
        }
    } else {
        assert(spec_partial_sum(ii, b, r) == r * (b + 1) + (ii - r) * b);
        assert(spec_partial_sum(ii + 1, b, r) == r * (b + 1) + (ii + 1 - r) * b);
        assert((r * (b + 1) + (ii + 1 - r) * b) - (r * (b + 1) + (ii - r) * b) == b) by (nonlinear_arith)
            requires
                0 <= r,
                0 <= b,
                r <= ii,
        {
        }
        assert(spec_partial_sum(ii + 1, b, r) == spec_partial_sum(ii, b, r) + b);
    }
}

proof fn lemma_sum_gift(i: int, b: int, r: int)
    requires
        i >= 0,
        0 <= r,
        0 <= b <= 100,
    ensures
        spec_seq_sum(spec_gift_seq(i, b, r), i) == spec_partial_sum(i, b, r),
    decreases i as nat,
{
    if i <= 0 {
        reveal_with_fuel(spec_seq_sum, 10);
        assert(spec_gift_seq(0, b, r).len() == 0);
    } else {
        lemma_sum_gift(i - 1, b, r);
        lemma_gift_seq_len(i - 1, b, r);
        let prev = spec_gift_seq(i - 1, b, r);
        let idx = i - 1;
        let tv = spec_tail_val(idx, b, r);
        assert(spec_gift_seq(i, b, r) == prev.push(tv));
        assert((i - 1) == prev.len());
        lemma_seq_sum_push(prev, i - 1, tv);
        assert(spec_seq_sum(prev.push(tv), i) == spec_seq_sum(prev, i - 1) + (tv as int));
        if idx < r {
            lemma_partial_sum_step_lt_rem(idx, b, r);
            assert(tv == (b + 1) as i32);
        } else {
            lemma_partial_sum_step_ge_rem(idx, b, r);
            assert(tv == b as i32);
        }
    }
}

proof fn lemma_tail_val_ge_b(j: int, b: int, r: int)
    requires
        1 <= b <= 100,
        0 <= j,
    ensures
        spec_tail_val(j, b, r) as int >= b,
{
    if j < r {
        assert(spec_tail_val(j, b, r) == (b + 1) as i32);
        assert((spec_tail_val(j, b, r) as int) == b + 1);
    } else {
        assert(spec_tail_val(j, b, r) == b as i32);
        assert((spec_tail_val(j, b, r) as int) == b);
    }
}

proof fn lemma_tail_val_in_range(j: int, b: int, r: int)
    requires
        0 <= b <= 100,
        0 <= j,
    ensures
        spec_tail_val(j, b, r) as int == b || spec_tail_val(j, b, r) as int == b + 1,
{
    if j < r {
        assert(spec_tail_val(j, b, r) == (b + 1) as i32);
        assert((spec_tail_val(j, b, r) as int) == b + 1);
    } else {
        assert(spec_tail_val(j, b, r) == b as i32);
        assert((spec_tail_val(j, b, r) as int) == b);
    }
}

proof fn lemma_gift_seq_index(i: int, b: int, r: int, j: int)
    requires
        i >= 1,
        0 <= b <= 100,
        0 <= j < i,
    ensures
        spec_gift_seq(i, b, r)[j] == spec_tail_val(j, b, r),
    decreases i as nat,
{
    lemma_gift_seq_len(i, b, r);
    assert(j < spec_gift_seq(i, b, r).len());
    if j < i - 1 {
        assert(spec_gift_seq(i, b, r) == spec_gift_seq(i - 1, b, r).push(spec_tail_val(i - 1, b, r)));
        lemma_gift_seq_len(i - 1, b, r);
        assert(j < spec_gift_seq(i - 1, b, r).len());
        lemma_gift_seq_index(i - 1, b, r, j);
        assert(spec_gift_seq(i, b, r)[j] == spec_gift_seq(i - 1, b, r)[j]);
        assert(spec_gift_seq(i - 1, b, r)[j] == spec_tail_val(j, b, r));
    } else {
        assert(j == i - 1);
        assert(spec_gift_seq(i, b, r) == spec_gift_seq(i - 1, b, r).push(spec_tail_val(i - 1, b, r)));
        lemma_gift_seq_len(i - 1, b, r);
        assert(spec_gift_seq(i, b, r).len() == i);
        assert(j < i);
        assert(spec_gift_seq(i, b, r)[j] == spec_tail_val(i - 1, b, r));
        assert(spec_tail_val(i - 1, b, r) == spec_tail_val(j, b, r));
    }
}

proof fn lemma_spec_seq_sum_le_k_times_bound(s: Seq<i32>, k: int, upper: int)
    requires
        0 < k <= s.len(),
        forall|j: int| 0 <= j < k ==> (#[trigger] s[j] as int) <= upper,
    ensures
        spec_seq_sum(s, k) <= k * upper,
    decreases k as nat,
{
    reveal_with_fuel(spec_seq_sum, 200);
    if k == 1 {
        assert(spec_seq_sum(s, 1) == s[0] as int);
        assert(s[0] as int <= upper);
    } else {
        lemma_spec_seq_sum_le_k_times_bound(s, k - 1, upper);
        assert(spec_seq_sum(s, k) == spec_seq_sum(s, k - 1) + s[k - 1] as int);
        assert(s[k - 1] as int <= upper);
        assert(spec_seq_sum(s, k - 1) <= (k - 1) * upper);
        assert(spec_seq_sum(s, k) <= (k - 1) * upper + upper);
        assert((k - 1) * upper + upper == k * upper) by (nonlinear_arith)
            requires
                true,
        {
        }
    }
}

proof fn lemma_seq_sum_le_m_times_max(s: Seq<i32>, k: int)
    requires
        0 < k <= s.len(),
    ensures
        spec_seq_sum(s, k) <= k * spec_seq_max(s, k),
{
    let t = s.take(k).map_values(|x| x as int);
    assert(t.len() == k);
    t.max_ensures();
    assert forall|j: int| 0 <= j < k implies (#[trigger] s[j] as int) <= spec_seq_max(s, k) by {
        assert(s[j] as int == t[j]);
        assert(t[j] <= t.max());
        assert(t.max() == spec_seq_max(s, k));
    }
    lemma_spec_seq_sum_le_k_times_bound(s, k, spec_seq_max(s, k));
}

proof fn lemma_spec_seq_sum_ge_k_times_bound(s: Seq<i32>, k: int, lower: int)
    requires
        0 < k <= s.len(),
        forall|j: int| 0 <= j < k ==> (#[trigger] s[j] as int) >= lower,
    ensures
        spec_seq_sum(s, k) >= k * lower,
    decreases k as nat,
{
    reveal_with_fuel(spec_seq_sum, 200);
    if k == 1 {
        assert(spec_seq_sum(s, 1) == s[0] as int);
        assert(s[0] as int >= lower);
    } else {
        lemma_spec_seq_sum_ge_k_times_bound(s, k - 1, lower);
        assert(spec_seq_sum(s, k) == spec_seq_sum(s, k - 1) + s[k - 1] as int);
        assert(s[k - 1] as int >= lower);
        assert(spec_seq_sum(s, k - 1) >= (k - 1) * lower);
        assert(spec_seq_sum(s, k) >= (k - 1) * lower + lower);
        assert((k - 1) * lower + lower == k * lower) by (nonlinear_arith)
            requires
                true,
        {
        }
    }
}

proof fn lemma_seq_sum_ge_m_times_min(s: Seq<i32>, k: int)
    requires
        0 < k <= s.len(),
    ensures
        spec_seq_sum(s, k) >= k * spec_seq_min(s, k),
{
    let t = s.take(k).map_values(|x| x as int);
    assert(t.len() == k);
    t.min_ensures();
    assert forall|j: int| 0 <= j < k implies (#[trigger] s[j] as int) >= spec_seq_min(s, k) by {
        assert(s[j] as int == t[j]);
        assert(t[j] >= t.min());
        assert(t.min() == spec_seq_min(s, k));
    }
    lemma_spec_seq_sum_ge_k_times_bound(s, k, spec_seq_min(s, k));
}

proof fn lemma_max_ge_ceil(n: int, m: int, mx: int)
    requires
        0 < m,
        0 <= n,
        n <= m * mx,
    ensures
        mx >= spec_int_ceil_div(n, m),
{
    assert(mx >= (n + m - 1) / m) by (nonlinear_arith)
        requires
            0 < m,
            n <= m * mx,
    {
    }
    assert(spec_int_ceil_div(n, m) == (n + m - 1) / m);
}

proof fn lemma_min_le_floor(n: int, m: int, mn: int)
    requires
        0 < m,
        0 <= n,
        n >= m * mn,
    ensures
        mn <= n / m,
{
    assert(mn <= n / m) by (nonlinear_arith)
        requires
            0 < m,
            n >= m * mn,
    {
    }
}

proof fn lemma_spread_ge_ceilm_floor(s: Seq<i32>, n: int, m: int)
    requires
        m >= 1,
        spec_valid_candy_split(s, n, m),
    ensures
        spec_seq_max(s, m) - spec_seq_min(s, m) >= spec_int_ceil_div(n, m) - n / m,
{
    assert(n >= m) by {
        assert forall|j: int| 0 <= j < m implies (#[trigger] s[j] as int) >= 1 by {
        }
        lemma_spec_seq_sum_ge_k_times_bound(s, m, 1);
        assert(spec_seq_sum(s, m) == n);
        assert(spec_seq_sum(s, m) >= m * 1);
    }
    assert(n >= 0);
    lemma_seq_sum_le_m_times_max(s, m);
    lemma_seq_sum_ge_m_times_min(s, m);
    let mx = spec_seq_max(s, m);
    let mn = spec_seq_min(s, m);
    assert(spec_seq_sum(s, m) == n);
    assert(n <= m * mx);
    assert(n >= m * mn);
    lemma_max_ge_ceil(n, m, mx);
    lemma_min_le_floor(n, m, mn);
    let hi = spec_int_ceil_div(n, m);
    let lo = n / m;
    assert(mx >= hi);
    assert(mn <= lo);
    assert(mx - mn >= hi - lo);
}

proof fn lemma_ceilm_floor_diff_from_n_mod(n: int, m: int)
    requires
        0 < m,
        0 <= n,
    ensures
        spec_int_ceil_div(n, m) - n / m == if n % m == 0 { 0int } else { 1int },
{
    lemma_fundamental_div_mod(n, m);
    let q = n / m;
    let r = n % m;
    assert(0 <= r < m);
    assert(n == m * q + r);
    if r == 0 {
        assert(spec_int_ceil_div(n, m) == (n + m - 1) / m);
        assert((n + m - 1) / m == q) by (nonlinear_arith)
            requires
                n == m * q,
                0 < m,
        {
        }
        assert(n / m == q);
        assert(spec_int_ceil_div(n, m) - n / m == 0);
    } else {
        assert(spec_int_ceil_div(n, m) == (n + m - 1) / m);
        assert((n + m - 1) / m == q + 1) by (nonlinear_arith)
            requires
                n == m * q + r,
                1 <= r < m,
                0 < m,
        {
        }
        assert(n / m == q);
        assert(spec_int_ceil_div(n, m) - n / m == 1);
    }
}

proof fn lemma_gift_spread_matches_ri(mi: int, bi: int, ri: int)
    requires
        mi >= 1,
        0 <= ri < mi,
        0 <= bi <= 100,
    ensures
        spec_seq_max(spec_gift_seq(mi, bi, ri), mi) - spec_seq_min(spec_gift_seq(mi, bi, ri), mi) == if ri == 0 {
            0int
        } else {
            1int
        },
{
    let g = spec_gift_seq(mi, bi, ri);
    lemma_gift_seq_len(mi, bi, ri);
    assert(g.len() == mi);
    let t = g.map_values(|x| x as int);
    assert(t.len() == mi);
    assert(t == g.take(mi).map_values(|x| x as int));
    assert(spec_seq_max(g, mi) == t.max());
    assert(spec_seq_min(g, mi) == t.min());
    if ri == 0 {
        assert forall|j: int| 0 <= j < mi implies (#[trigger] t[j]) == bi by {
            lemma_gift_seq_index(mi, bi, ri, j);
            assert(g[j] == spec_tail_val(j, bi, ri));
            assert(!(j < ri));
            assert(spec_tail_val(j, bi, ri) == bi as i32);
        }
        t.max_ensures();
        t.min_ensures();
        assert(forall|i: int| 0 <= i < t.len() ==> t[i] == bi);
        assert(t.max() == bi);
        assert(t.min() == bi);
        assert(spec_seq_max(g, mi) - spec_seq_min(g, mi) == 0);
    } else {
        lemma_gift_seq_index(mi, bi, ri, 0);
        lemma_gift_seq_index(mi, bi, ri, mi - 1);
        assert(spec_tail_val(0, bi, ri) == (bi + 1) as i32);
        assert(spec_tail_val(mi - 1, bi, ri) == bi as i32);
        assert(t[0] == bi + 1);
        assert(t[mi - 1] == bi);
        assert forall|j: int| 0 <= j < mi implies bi <= (#[trigger] t[j]) && (#[trigger] t[j]) <= bi + 1 by {
            lemma_gift_seq_index(mi, bi, ri, j);
            assert(g[j] == spec_tail_val(j, bi, ri));
            lemma_tail_val_in_range(j, bi, ri);
            let v = spec_tail_val(j, bi, ri) as int;
            assert(v == bi || v == bi + 1);
        }
        t.max_ensures();
        t.min_ensures();
        assert(t.max() == bi + 1);
        assert(t.min() == bi);
        assert(spec_seq_max(g, mi) - spec_seq_min(g, mi) == 1);
    }
}

impl Solution {
    pub fn fair_candy_split(n: i32, m: i32) -> (result: Vec<i32>)
        requires
            1 <= m <= n <= 100,
        ensures
            spec_valid_candy_split(result@, n as int, m as int),
            exists|t: Seq<i32>|
                spec_valid_candy_split(t, n as int, m as int) && t == result@,
            forall|s: Seq<i32>|
                spec_valid_candy_split(s, n as int, m as int) ==> {
                    let spread_s = spec_seq_max(s, m as int) - spec_seq_min(s, m as int);
                    let spread_r = spec_seq_max(result@, m as int) - spec_seq_min(result@, m as int);
                    spread_s >= spread_r
                },
    {
        let base = n / m;
        let rem = n % m;
        proof {
            lemma_base_pos(n, m, base);
            lemma_rem_range(n, m, rem);
            lemma_div_identity(n, m, base, rem);
        }
        let mut v: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mu = m as usize;
        while i < mu
            invariant
                1 <= m,
                m <= n,
                n <= 100,
                mu == m as usize,
                base == n / m,
                rem == n % m,
                i <= mu,
                v@ == spec_gift_seq(i as int, base as int, rem as int),
            decreases mu - i,
        {
            proof {
                lemma_base_pos(n, m, base);
                assert((base as int) <= 100);
                assert((base as int) + 1 <= 101);
            }
            let val = if i < rem as usize { base + 1 } else { base };
            proof {
                assert(val == spec_tail_val(i as int, base as int, rem as int));
                lemma_gift_push(i as int, base as int, rem as int, val);
            }
            v.push(val);
            proof {
                assert(v@ == spec_gift_seq((i + 1) as int, base as int, rem as int));
            }
            i = i + 1;
        }
        proof {
            assert(i == mu);
            let mi = m as int;
            let bi = base as int;
            let ri = rem as int;
            lemma_gift_seq_len(mi, bi, ri);
            assert(v@.len() == mi);
            assert(0 <= ri);
            assert(0 <= bi && bi <= 100);
            lemma_sum_gift(mi, bi, ri);
            assert(spec_seq_sum(v@, mi) == spec_partial_sum(mi, bi, ri));
            lemma_partial_total(mi, bi, ri);
            assert(spec_partial_sum(mi, bi, ri) == mi * bi + ri);
            assert((n as int) == mi * bi + ri);
            assert(spec_seq_sum(v@, mi) == n as int);
            assert(forall|j: int|
                0 <= j < mi ==> (#[trigger] v@[j] as int) >= 1) by {
                assert(bi >= 1);
                assert forall|j: int| 0 <= j < mi implies (#[trigger] v@[j] as int) >= 1 by {
                    lemma_gift_seq_index(mi, bi, ri, j);
                    assert(v@[j] == spec_gift_seq(mi, bi, ri)[j]);
                    lemma_tail_val_ge_b(j, bi, ri);
                }
            };
            assert(spec_valid_candy_split(v@, n as int, m as int));
            assert(exists|t: Seq<i32>| spec_valid_candy_split(t, n as int, m as int) && t == v@);
            assert forall|s: Seq<i32>|
                spec_valid_candy_split(s, n as int, m as int) implies {
                    let spread_s = spec_seq_max(s, m as int) - spec_seq_min(s, m as int);
                    let spread_r = spec_seq_max(v@, m as int) - spec_seq_min(v@, m as int);
                    spread_s >= spread_r
                }
            by {
                assert forall|s: Seq<i32>|
                    spec_valid_candy_split(s, n as int, m as int) implies {
                        let spread_s = spec_seq_max(s, m as int) - spec_seq_min(s, m as int);
                        let spread_r = spec_seq_max(v@, m as int) - spec_seq_min(v@, m as int);
                        spread_s >= spread_r
                    }
                by {
                    let ni = n as int;
                    lemma_spread_ge_ceilm_floor(s, ni, mi);
                    lemma_ceilm_floor_diff_from_n_mod(ni, mi);
                    lemma_gift_spread_matches_ri(mi, bi, ri);
                    lemma_div_identity(n, m, base, rem);
                    assert(ri == ni % mi);
                    let bound = spec_int_ceil_div(ni, mi) - ni / mi;
                    assert(spec_seq_max(v@, mi) - spec_seq_min(v@, mi) == bound);
                    assert(spec_seq_max(s, mi) - spec_seq_min(s, mi) >= bound);
                    let spread_s = spec_seq_max(s, mi) - spec_seq_min(s, mi);
                    let spread_r = spec_seq_max(v@, mi) - spec_seq_min(v@, mi);
                    assert(spread_s >= spread_r);
                }
            };
        }
        v
    }
}

}
