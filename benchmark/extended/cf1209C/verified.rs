use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_c1_values(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = spec_c1_values(d, c, n - 1);
        if c[n - 1] == 1 {
            rest + seq![d[n - 1]]
        } else {
            rest
        }
    }
}

pub open spec fn spec_c2_values(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = spec_c2_values(d, c, n - 1);
        if c[n - 1] == 2 {
            rest + seq![d[n - 1]]
        } else {
            rest
        }
    }
}

pub open spec fn spec_merged_digits(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32> {
    spec_c1_values(d, c, n) + spec_c2_values(d, c, n)
}

pub open spec fn spec_adjacent_nondecreasing(s: Seq<i32>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() - 1 ==> s[i] <= s[i + 1]
}

pub open spec fn spec_valid_coloring(d: Seq<i32>, c: Seq<i32>) -> bool {
    d.len() == c.len()
        && (forall|i: int| 0 <= i < d.len() ==> #[trigger] c[i] == 1 || c[i] == 2)
        && spec_adjacent_nondecreasing(spec_merged_digits(d, c, d.len() as int))
}

proof fn lemma_spec_c1_step(d: Seq<i32>, c: Seq<i32>, i: int)
    requires
        0 <= i < d.len(),
        c.len() == d.len(),
    ensures
        spec_c1_values(d, c, i + 1)
            == if c[i] == 1 {
                spec_c1_values(d, c, i) + seq![d[i]]
            } else {
                spec_c1_values(d, c, i)
            },
{
    assert((i + 1) - 1 == i);
    assert(spec_c1_values(d, c, i + 1) == ({
        let rest = spec_c1_values(d, c, i);
        if c[i] == 1 {
            rest + seq![d[i]]
        } else {
            rest
        }
    }));
}

proof fn lemma_spec_c2_step(d: Seq<i32>, c: Seq<i32>, i: int)
    requires
        0 <= i < d.len(),
        c.len() == d.len(),
    ensures
        spec_c2_values(d, c, i + 1)
            == if c[i] == 2 {
                spec_c2_values(d, c, i) + seq![d[i]]
            } else {
                spec_c2_values(d, c, i)
            },
{
    assert((i + 1) - 1 == i);
    assert(spec_c2_values(d, c, i + 1) == ({
        let rest = spec_c2_values(d, c, i);
        if c[i] == 2 {
            rest + seq![d[i]]
        } else {
            rest
        }
    }));
}

proof fn lemma_adjacent_from_prefix(merged: Seq<i32>, n: int)
    requires
        n == merged.len(),
        forall|t: int| #![trigger merged[t]] 0 <= t < n - 1 ==> merged[t] <= merged[t + 1],
    ensures
        spec_adjacent_nondecreasing(merged),
{
}

proof fn lemma_lens_add_n(d: Seq<i32>, c: Seq<i32>, n: int)
    requires
        n >= 0,
        d.len() >= n,
        c.len() >= n,
        forall|i: int| #![trigger c[i]] 0 <= i < n ==> c[i] == 1 || c[i] == 2,
    ensures
        spec_c1_values(d, c, n).len() + spec_c2_values(d, c, n).len() == n,
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_lens_add_n(d, c, n - 1);
        assert(0 <= n - 1 < c.len());
        assert(c[n - 1] == 1 || c[n - 1] == 2);
        let prev_sum = spec_c1_values(d, c, n - 1).len() + spec_c2_values(d, c, n - 1).len();
        let cur_sum = spec_c1_values(d, c, n).len() + spec_c2_values(d, c, n).len();
        assert(cur_sum == prev_sum + 1);
    }
}

pub open spec fn spec_exists_valid_coloring(d: Seq<i32>) -> bool {
    exists|c: Seq<i32>| spec_valid_coloring(d, c)
}

pub open spec fn spec_count_before(c: Seq<i32>, i: int, color: i32) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        spec_count_before(c, i - 1, color) + (if c[i - 1] == color { 1int } else { 0int })
    }
}

proof fn lemma_count_before_nonneg(c: Seq<i32>, i: int, color: i32)
    requires
        i >= 0,
    ensures
        spec_count_before(c, i, color) >= 0,
    decreases i,
{
    if i > 0 {
        lemma_count_before_nonneg(c, i - 1, color);
    }
}

proof fn lemma_count_before_eq_len(d: Seq<i32>, c: Seq<i32>, k: int)
    requires
        c.len() == d.len(),
        0 <= k <= d.len(),
    ensures
        spec_count_before(c, k, 1) == spec_c1_values(d, c, k).len(),
    decreases k,
{
    if k > 0 {
        lemma_count_before_eq_len(d, c, k - 1);
    }
}

proof fn lemma_c1_index_mapping(d: Seq<i32>, c: Seq<i32>, n: int, i: int)
    requires
        c.len() == d.len(),
        d.len() >= n,
        0 <= i < n,
        c[i] == 1,
    ensures
        spec_count_before(c, i, 1) < spec_c1_values(d, c, n).len(),
        spec_c1_values(d, c, n)[spec_count_before(c, i, 1)] == d[i],
    decreases n,
{
    lemma_count_before_nonneg(c, i, 1);
    if i == n - 1 {
        assert(spec_c1_values(d, c, n) == spec_c1_values(d, c, n - 1) + seq![d[n - 1]]);
        lemma_count_before_eq_len(d, c, i);
        assert(spec_count_before(c, i, 1) == spec_c1_values(d, c, n - 1).len());
        let a = spec_c1_values(d, c, n - 1);
        assert((a + seq![d[n - 1]])[a.len() as int] == d[n - 1]);
        assert(spec_c1_values(d, c, n)[spec_count_before(c, i, 1)] == d[i]);
    } else {
        lemma_c1_index_mapping(d, c, n - 1, i);
        if c[n - 1] == 1 {
            let a = spec_c1_values(d, c, n - 1);
            let idx: int = spec_count_before(c, i, 1);
            assert(0 <= idx < a.len());
            assert(a[idx] == d[i]);
            assert(spec_c1_values(d, c, n) == a + seq![d[n - 1]]);
            assert((a + seq![d[n - 1]]).len() == a.len() + 1);
            assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] (a + seq![d[n - 1]])[k] == a[k]);
            assert((a + seq![d[n - 1]])[idx] == a[idx]);
            assert(spec_c1_values(d, c, n)[idx] == d[i]);
        } else {
            assert(spec_c1_values(d, c, n) == spec_c1_values(d, c, n - 1));
        }
    }
}

proof fn lemma_count_before2_nonneg(c: Seq<i32>, i: int, color: i32)
    requires
        i >= 0,
    ensures
        spec_count_before(c, i, color) >= 0,
    decreases i,
{
    if i > 0 {
        lemma_count_before2_nonneg(c, i - 1, color);
    }
}

proof fn lemma_count_before_eq_len2(d: Seq<i32>, c: Seq<i32>, k: int)
    requires
        c.len() == d.len(),
        0 <= k <= d.len(),
    ensures
        spec_count_before(c, k, 2) == spec_c2_values(d, c, k).len(),
    decreases k,
{
    if k > 0 {
        lemma_count_before_eq_len2(d, c, k - 1);
    }
}

proof fn lemma_c2_index_mapping(d: Seq<i32>, c: Seq<i32>, n: int, i: int)
    requires
        c.len() == d.len(),
        d.len() >= n,
        0 <= i < n,
        c[i] == 2,
    ensures
        spec_count_before(c, i, 2) < spec_c2_values(d, c, n).len(),
        spec_c2_values(d, c, n)[spec_count_before(c, i, 2)] == d[i],
    decreases n,
{
    lemma_count_before2_nonneg(c, i, 2);
    if i == n - 1 {
        assert(spec_c2_values(d, c, n) == spec_c2_values(d, c, n - 1) + seq![d[n - 1]]);
        lemma_count_before_eq_len2(d, c, i);
        assert(spec_count_before(c, i, 2) == spec_c2_values(d, c, n - 1).len());
        let a = spec_c2_values(d, c, n - 1);
        assert((a + seq![d[n - 1]])[a.len() as int] == d[n - 1]);
        assert(spec_c2_values(d, c, n)[spec_count_before(c, i, 2)] == d[i]);
    } else {
        lemma_c2_index_mapping(d, c, n - 1, i);
        if c[n - 1] == 2 {
            let a = spec_c2_values(d, c, n - 1);
            let idx: int = spec_count_before(c, i, 2);
            assert(0 <= idx < a.len());
            assert(a[idx] == d[i]);
            assert(spec_c2_values(d, c, n) == a + seq![d[n - 1]]);
            assert(forall|k: int| 0 <= k < a.len() ==> #[trigger] (a + seq![d[n - 1]])[k] == a[k]);
            assert((a + seq![d[n - 1]])[idx] == a[idx]);
            assert(spec_c2_values(d, c, n)[idx] == d[i]);
        } else {
            assert(spec_c2_values(d, c, n) == spec_c2_values(d, c, n - 1));
        }
    }
}

proof fn lemma_count_before_monotonic(c: Seq<i32>, i: int, j: int, color: i32)
    requires
        0 <= i <= j,
    ensures
        spec_count_before(c, i, color) <= spec_count_before(c, j, color),
    decreases j - i,
{
    if i < j {
        lemma_count_before_monotonic(c, i, j - 1, color);
        assert(spec_count_before(c, j, color) == spec_count_before(c, j - 1, color)
            + (if c[j - 1] == color { 1int } else { 0int }));
    }
}

proof fn lemma_count_before_strict(c: Seq<i32>, i: int, j: int, color: i32)
    requires
        0 <= i < j,
        c[i] == color,
    ensures
        spec_count_before(c, i, color) < spec_count_before(c, j, color),
{
    assert(spec_count_before(c, i + 1, color) == spec_count_before(c, i, color)
        + (if c[i] == color { 1int } else { 0int }));
    lemma_count_before_monotonic(c, i + 1, j, color);
}

proof fn lemma_merged_pos_c1(d: Seq<i32>, c: Seq<i32>, n: int, k: int)
    requires
        0 <= k < spec_c1_values(d, c, n).len(),
    ensures
        spec_merged_digits(d, c, n)[k] == spec_c1_values(d, c, n)[k],
{
    let c1 = spec_c1_values(d, c, n);
    let c2 = spec_c2_values(d, c, n);
    assert(spec_merged_digits(d, c, n) == c1 + c2);
    assert((c1 + c2)[k] == c1[k]);
}

proof fn lemma_merged_pos_c2(d: Seq<i32>, c: Seq<i32>, n: int, k: int)
    requires
        0 <= k < spec_c2_values(d, c, n).len(),
    ensures
        spec_merged_digits(d, c, n)[spec_c1_values(d, c, n).len() as int + k] == spec_c2_values(d, c, n)[k],
{
    let c1 = spec_c1_values(d, c, n);
    let c2 = spec_c2_values(d, c, n);
    assert(spec_merged_digits(d, c, n) == c1 + c2);
    assert((c1 + c2)[c1.len() as int + k] == c2[k]);
}

pub open spec fn spec_max_color1(d: Seq<i32>, c: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        -1
    } else {
        let rest = spec_max_color1(d, c, n - 1);
        if c[n - 1] == 1 {
            if (d[n - 1] as int) > rest { d[n - 1] as int } else { rest }
        } else {
            rest
        }
    }
}

pub open spec fn spec_argmax_color1(d: Seq<i32>, c: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        -1
    } else {
        let rest_idx = spec_argmax_color1(d, c, n - 1);
        let rest_val = spec_max_color1(d, c, n - 1);
        if c[n - 1] == 1 {
            if rest_idx == -1 || (d[n - 1] as int) > rest_val { n - 1 } else { rest_idx }
        } else {
            rest_idx
        }
    }
}

proof fn lemma_max_color1_bounds(d: Seq<i32>, c: Seq<i32>, n: int)
    requires
        c.len() == d.len(),
        d.len() >= n,
    ensures
        forall|i: int| 0 <= i < n && c[i] == 1 ==> d[i] as int <= spec_max_color1(d, c, n),
    decreases n,
{
    if n > 0 {
        lemma_max_color1_bounds(d, c, n - 1);
    }
}

proof fn lemma_argmax_neg1_iff_max_neg1(d: Seq<i32>, c: Seq<i32>, n: int)
    requires
        c.len() == d.len(),
        d.len() >= n,
        n >= 0,
        forall|k: int| 0 <= k < d.len() ==> 0 <= d[k] as int,
    ensures
        spec_argmax_color1(d, c, n) == -1 <==> spec_max_color1(d, c, n) == -1,
    decreases n,
{
    if n > 0 {
        lemma_argmax_neg1_iff_max_neg1(d, c, n - 1);
        if c[n - 1] == 1 {
            if spec_argmax_color1(d, c, n - 1) == -1 {
                assert(spec_max_color1(d, c, n - 1) == -1);
                assert(d[n - 1] as int >= 0);
                assert((d[n - 1] as int) > spec_max_color1(d, c, n - 1));
                assert(spec_argmax_color1(d, c, n) == n - 1);
                assert(spec_max_color1(d, c, n) == d[n - 1] as int);
                assert(n - 1 != -1);
            } else if (d[n - 1] as int) > spec_max_color1(d, c, n - 1) {
                assert(spec_argmax_color1(d, c, n) == n - 1);
                assert(spec_max_color1(d, c, n) == d[n - 1] as int);
            } else {
                assert(spec_argmax_color1(d, c, n) == spec_argmax_color1(d, c, n - 1));
                assert(spec_max_color1(d, c, n) == spec_max_color1(d, c, n - 1));
            }
        } else {
            assert(spec_argmax_color1(d, c, n) == spec_argmax_color1(d, c, n - 1));
            assert(spec_max_color1(d, c, n) == spec_max_color1(d, c, n - 1));
        }
    }
}

proof fn lemma_argmax_color1_achieves(d: Seq<i32>, c: Seq<i32>, n: int)
    requires
        c.len() == d.len(),
        d.len() >= n,
        n >= 0,
        forall|k: int| 0 <= k < d.len() ==> 0 <= d[k] as int,
        spec_max_color1(d, c, n) > -1,
    ensures
        0 <= spec_argmax_color1(d, c, n) < n,
        c[spec_argmax_color1(d, c, n)] == 1,
        d[spec_argmax_color1(d, c, n)] as int == spec_max_color1(d, c, n),
    decreases n,
{
    lemma_argmax_neg1_iff_max_neg1(d, c, n - 1);
    if c[n - 1] == 1 && ((spec_max_color1(d, c, n - 1) == -1)
        || (d[n - 1] as int) > spec_max_color1(d, c, n - 1)) {
        assert(spec_argmax_color1(d, c, n) == n - 1);
        assert(spec_max_color1(d, c, n) == d[n - 1] as int);
    } else {
        lemma_argmax_color1_achieves(d, c, n - 1);
    }
}

pub open spec fn spec_threshold(d: Seq<i32>, c: Seq<i32>) -> int {
    let m = spec_max_color1(d, c, d.len() as int);
    if m < 0 { 0 } else { m }
}

proof fn lemma_threshold_compat(d: Seq<i32>, c: Seq<i32>)
    requires
        spec_valid_coloring(d, c),
        forall|k: int| 0 <= k < d.len() ==> 0 <= #[trigger] d[k] as int <= 9,
    ensures
        0 <= spec_threshold(d, c) <= 9,
        forall|i: int| 0 <= i < d.len() && c[i] == 1 ==> d[i] as int <= spec_threshold(d, c),
        forall|i: int| 0 <= i < d.len() && c[i] == 2 ==> d[i] as int >= spec_threshold(d, c),
{
    let n = d.len() as int;
    let m = spec_max_color1(d, c, n);
    lemma_max_color1_bounds(d, c, n);
    assert(forall|i: int| 0 <= i < n && c[i] == 1 ==> d[i] as int <= m);

    if m >= 0 {
        assert(spec_threshold(d, c) == m);
        lemma_argmax_color1_achieves(d, c, n);
        let i0 = spec_argmax_color1(d, c, n);
        assert(0 <= i0 < n && c[i0] == 1 && d[i0] as int == m);
        lemma_c1_index_mapping(d, c, n, i0);
        lemma_count_before_nonneg(c, i0, 1);
        let pos0 = spec_count_before(c, i0, 1);
        assert(spec_c1_values(d, c, n)[pos0] == d[i0]);
        lemma_merged_pos_c1(d, c, n, pos0);
        assert(spec_merged_digits(d, c, n)[pos0] == d[i0]);

        assert forall|j: int| 0 <= j < n && c[j] == 2 implies d[j] as int >= m by {
            lemma_c2_index_mapping(d, c, n, j);
            lemma_count_before2_nonneg(c, j, 2);
            let posj = spec_c1_values(d, c, n).len() as int + spec_count_before(c, j, 2);
            lemma_merged_pos_c2(d, c, n, spec_count_before(c, j, 2));
            assert(spec_merged_digits(d, c, n)[posj] == spec_c2_values(d, c, n)[spec_count_before(c, j, 2)]);
            assert(spec_merged_digits(d, c, n)[posj] == d[j]);
            assert(pos0 < posj);
            assert(pos0 < spec_merged_digits(d, c, n).len());
            assert(posj < spec_merged_digits(d, c, n).len());
            lemma_nondecreasing_transitive(spec_merged_digits(d, c, n), pos0, posj);
            assert(spec_merged_digits(d, c, n)[pos0] <= spec_merged_digits(d, c, n)[posj]);
        };
    } else {
        assert(spec_threshold(d, c) == 0);
        assert forall|i: int| 0 <= i < n && c[i] == 1 implies false by {
            assert(d[i] as int <= m);
        };
        assert forall|j: int| 0 <= j < n && c[j] == 2 implies d[j] as int >= 0 by {
        };
    }
}

pub open spec fn spec_kth_color1_pos(c: Seq<i32>, k: int, n: int) -> int
    decreases n,
{
    if n <= 0 {
        -1
    } else if c[n - 1] == 1 && spec_count_before(c, n - 1, 1) == k {
        n - 1
    } else {
        spec_kth_color1_pos(c, k, n - 1)
    }
}

proof fn lemma_kth_color1_pos_valid(d: Seq<i32>, c: Seq<i32>, n: int, k: int)
    requires
        c.len() == d.len(),
        d.len() >= n,
        0 <= k < spec_c1_values(d, c, n).len(),
    ensures
        0 <= spec_kth_color1_pos(c, k, n) < n,
        c[spec_kth_color1_pos(c, k, n)] == 1,
        spec_count_before(c, spec_kth_color1_pos(c, k, n), 1) == k,
        spec_c1_values(d, c, n)[k] == d[spec_kth_color1_pos(c, k, n)],
    decreases n,
{
    lemma_count_before_eq_len(d, c, n);
    if c[n - 1] == 1 && spec_count_before(c, n - 1, 1) == k {
        lemma_c1_index_mapping(d, c, n, n - 1);
    } else {
        if c[n - 1] == 1 {
            assert(spec_c1_values(d, c, n) == spec_c1_values(d, c, n - 1) + seq![d[n - 1]]);
            lemma_count_before_eq_len(d, c, n - 1);
        } else {
            assert(spec_c1_values(d, c, n) == spec_c1_values(d, c, n - 1));
        }
        lemma_kth_color1_pos_valid(d, c, n - 1, k);
    }
}

pub open spec fn spec_kth_color2_pos(c: Seq<i32>, k: int, n: int) -> int
    decreases n,
{
    if n <= 0 {
        -1
    } else if c[n - 1] == 2 && spec_count_before(c, n - 1, 2) == k {
        n - 1
    } else {
        spec_kth_color2_pos(c, k, n - 1)
    }
}

proof fn lemma_kth_color2_pos_valid(d: Seq<i32>, c: Seq<i32>, n: int, k: int)
    requires
        c.len() == d.len(),
        d.len() >= n,
        0 <= k < spec_c2_values(d, c, n).len(),
    ensures
        0 <= spec_kth_color2_pos(c, k, n) < n,
        c[spec_kth_color2_pos(c, k, n)] == 2,
        spec_count_before(c, spec_kth_color2_pos(c, k, n), 2) == k,
        spec_c2_values(d, c, n)[k] == d[spec_kth_color2_pos(c, k, n)],
    decreases n,
{
    lemma_count_before_eq_len2(d, c, n);
    if c[n - 1] == 2 && spec_count_before(c, n - 1, 2) == k {
        lemma_c2_index_mapping(d, c, n, n - 1);
    } else {
        if c[n - 1] == 2 {
            assert(spec_c2_values(d, c, n) == spec_c2_values(d, c, n - 1) + seq![d[n - 1]]);
            lemma_count_before_eq_len2(d, c, n - 1);
        } else {
            assert(spec_c2_values(d, c, n) == spec_c2_values(d, c, n - 1));
        }
        lemma_kth_color2_pos_valid(d, c, n - 1, k);
    }
}

proof fn lemma_c1_sorted(d: Seq<i32>, c: Seq<i32>)
    requires
        spec_valid_coloring(d, c),
    ensures
        spec_adjacent_nondecreasing(spec_c1_values(d, c, d.len() as int)),
{
    let n = d.len() as int;
    let c1 = spec_c1_values(d, c, n);
    assert forall|p: int| 0 <= p < c1.len() - 1 implies #[trigger] c1[p] <= c1[p + 1] by {
        lemma_kth_color1_pos_valid(d, c, n, p);
        lemma_kth_color1_pos_valid(d, c, n, p + 1);
        let i = spec_kth_color1_pos(c, p, n);
        let j = spec_kth_color1_pos(c, p + 1, n);
        assert(i < j) by {
            if i >= j {
                lemma_count_before_monotonic(c, j, i, 1);
            }
        };
        lemma_merged_pos_c1(d, c, n, p);
        lemma_merged_pos_c1(d, c, n, p + 1);
        lemma_nondecreasing_transitive(spec_merged_digits(d, c, n), p, p + 1);
    };
}

proof fn lemma_c2_sorted(d: Seq<i32>, c: Seq<i32>)
    requires
        spec_valid_coloring(d, c),
    ensures
        spec_adjacent_nondecreasing(spec_c2_values(d, c, d.len() as int)),
{
    let n = d.len() as int;
    let c1 = spec_c1_values(d, c, n);
    let c2 = spec_c2_values(d, c, n);
    assert forall|p: int| 0 <= p < c2.len() - 1 implies #[trigger] c2[p] <= c2[p + 1] by {
        lemma_kth_color2_pos_valid(d, c, n, p);
        lemma_kth_color2_pos_valid(d, c, n, p + 1);
        let i = spec_kth_color2_pos(c, p, n);
        let j = spec_kth_color2_pos(c, p + 1, n);
        assert(i < j) by {
            if i >= j {
                lemma_count_before_monotonic(c, j, i, 2);
            }
        };
        lemma_merged_pos_c2(d, c, n, p);
        lemma_merged_pos_c2(d, c, n, p + 1);
        assert(c1.len() as int + p < c1.len() as int + p + 1);
        assert(c1.len() as int + (p + 1) < spec_merged_digits(d, c, n).len());
        lemma_nondecreasing_transitive(spec_merged_digits(d, c, n), c1.len() as int + p, c1.len() as int + p + 1);
    };
}

proof fn lemma_c1_last_is_max(d: Seq<i32>, c: Seq<i32>)
    requires
        spec_valid_coloring(d, c),
        forall|k: int| 0 <= k < d.len() ==> 0 <= #[trigger] d[k] as int,
        spec_c1_values(d, c, d.len() as int).len() > 0,
    ensures
        spec_c1_values(d, c, d.len() as int).last() as int
            == spec_max_color1(d, c, d.len() as int),
{
    let n = d.len() as int;
    let c1 = spec_c1_values(d, c, n);
    lemma_c1_sorted(d, c);
    lemma_max_color1_bounds(d, c, n);
    lemma_kth_color1_pos_valid(d, c, n, c1.len() as int - 1);
    let ilast = spec_kth_color1_pos(c, c1.len() as int - 1, n);
    assert(c1[c1.len() as int - 1] == d[ilast]);
    assert(c1.last() == c1[c1.len() as int - 1]);
    assert(d[ilast] as int <= spec_max_color1(d, c, n));

    lemma_argmax_color1_achieves(d, c, n);
    let i0 = spec_argmax_color1(d, c, n);
    lemma_c1_index_mapping(d, c, n, i0);
    lemma_count_before_nonneg(c, i0, 1);
    let pos0 = spec_count_before(c, i0, 1);
    assert(0 <= pos0 < c1.len());
    assert forall|q: int| pos0 <= q < c1.len() as int implies #[trigger] c1[pos0] <= c1[q] by {
        if pos0 < q {
            lemma_nondecreasing_c1_range(d, c, pos0, q);
        }
    };
    assert(c1[pos0] == d[i0]);
    assert(c1[c1.len() as int - 1] >= c1[pos0]);
    assert(d[i0] as int == spec_max_color1(d, c, n));
}

proof fn lemma_nondecreasing_c1_range(d: Seq<i32>, c: Seq<i32>, p: int, q: int)
    requires
        spec_valid_coloring(d, c),
        0 <= p <= q < spec_c1_values(d, c, d.len() as int).len(),
    ensures
        spec_c1_values(d, c, d.len() as int)[p] <= spec_c1_values(d, c, d.len() as int)[q],
{
    lemma_c1_sorted(d, c);
    lemma_nondecreasing_transitive(spec_c1_values(d, c, d.len() as int), p, q);
}

proof fn lemma_color1_pair_ordered(d: Seq<i32>, c: Seq<i32>, i: int, j: int)
    requires
        spec_valid_coloring(d, c),
        0 <= i < j < d.len(),
        c[i] == 1,
        c[j] == 1,
    ensures
        d[i] as int <= d[j] as int,
{
    let n = d.len() as int;
    lemma_c1_sorted(d, c);
    lemma_c1_index_mapping(d, c, n, i);
    lemma_c1_index_mapping(d, c, n, j);
    let pi = spec_count_before(c, i, 1);
    let pj = spec_count_before(c, j, 1);
    lemma_count_before_strict(c, i, j, 1);
    lemma_count_before_nonneg(c, i, 1);
    lemma_nondecreasing_transitive(spec_c1_values(d, c, n), pi, pj);
}

proof fn lemma_color2_pair_ordered(d: Seq<i32>, c: Seq<i32>, i: int, j: int)
    requires
        spec_valid_coloring(d, c),
        0 <= i < j < d.len(),
        c[i] == 2,
        c[j] == 2,
    ensures
        d[i] as int <= d[j] as int,
{
    let n = d.len() as int;
    lemma_c2_sorted(d, c);
    lemma_c2_index_mapping(d, c, n, i);
    lemma_c2_index_mapping(d, c, n, j);
    let pi = spec_count_before(c, i, 2);
    let pj = spec_count_before(c, j, 2);
    lemma_count_before_strict(c, i, j, 2);
    lemma_count_before2_nonneg(c, i, 2);
    lemma_nondecreasing_transitive(spec_c2_values(d, c, n), pi, pj);
}

proof fn lemma_eqx_before_smaller_forces_color2(d: Seq<i32>, c: Seq<i32>, x: int, j: int, p: int)
    requires
        spec_valid_coloring(d, c),
        forall|k: int| 0 <= k < d.len() && c[k] == 1 ==> d[k] as int <= x,
        forall|k: int| 0 <= k < d.len() && c[k] == 2 ==> d[k] as int >= x,
        0 <= j < p < d.len(),
        d[j] as int == x,
        (d[p] as int) < x,
    ensures
        c[j] == 2,
{
    if c[j] == 1 {
        assert(c[p] == 1) by {
            if c[p] == 2 {
                assert(d[p] as int >= x);
            }
        };
        lemma_color1_pair_ordered(d, c, j, p);
        assert(d[j] as int <= d[p] as int);
    }
}

proof fn lemma_merged_sorted_from_parts(d: Seq<i32>, e: Seq<i32>, n: int)
    requires
        e.len() == n,
        d.len() >= n,
        n >= 0,
        forall|k: int| 0 <= k < n ==> #[trigger] e[k] == 1 || e[k] == 2,
        spec_adjacent_nondecreasing(spec_c1_values(d, e, n)),
        spec_adjacent_nondecreasing(spec_c2_values(d, e, n)),
        spec_c1_values(d, e, n).len() > 0 && spec_c2_values(d, e, n).len() > 0 ==>
            spec_c1_values(d, e, n).last() as int <= spec_c2_values(d, e, n).first() as int,
    ensures
        spec_adjacent_nondecreasing(spec_merged_digits(d, e, n)),
{
    let c1 = spec_c1_values(d, e, n);
    let c2 = spec_c2_values(d, e, n);
    let m = spec_merged_digits(d, e, n);
    assert(m == c1 + c2);
    assert forall|p: int| 0 <= p < m.len() - 1 implies #[trigger] m[p] <= m[p + 1] by {
        if p + 1 < c1.len() {
            assert(m[p] == c1[p]);
            assert(m[p + 1] == c1[p + 1]);
        } else if p >= c1.len() as int {
            assert(m[p] == c2[p - c1.len() as int]);
            assert(m[p + 1] == c2[p + 1 - c1.len() as int]);
        } else {
            assert(p == c1.len() as int - 1);
            assert(m[p] == c1[p]);
            assert(c1[p] == c1.last());
            assert(m[p + 1] == c2[0]);
            assert(c2[0] == c2.first());
        }
    };
}

pub open spec fn spec_last_lt(d: Seq<i32>, x: int, upto: int) -> int
    decreases upto,
{
    if upto <= 0 {
        d.len() as int
    } else {
        let prev = spec_last_lt(d, x, upto - 1);
        if (d[upto - 1] as int) < x { upto - 1 } else { prev }
    }
}

proof fn lemma_last_lt_props(d: Seq<i32>, x: int, upto: int)
    requires
        0 <= upto <= d.len(),
    ensures
        spec_last_lt(d, x, upto) == d.len() as int
            || (0 <= spec_last_lt(d, x, upto) < upto && (d[spec_last_lt(d, x, upto)] as int) < x),
        spec_last_lt(d, x, upto) == d.len() as int ==>
            forall|k: int| 0 <= k < upto ==> (#[trigger] d[k] as int) >= x,
        spec_last_lt(d, x, upto) != d.len() as int ==>
            forall|k: int| spec_last_lt(d, x, upto) < k < upto ==> (#[trigger] d[k] as int) >= x,
    decreases upto,
{
    if upto > 0 {
        lemma_last_lt_props(d, x, upto - 1);
    }
}

pub open spec fn spec_pivot_color(d: Seq<i32>, x: int, i: int, last_lt: int) -> i32 {
    if (d[i] as int) < x {
        1
    } else if (d[i] as int) > x {
        2
    } else if last_lt != d.len() as int && i <= last_lt {
        2
    } else {
        1
    }
}

pub open spec fn spec_pivot_coloring(d: Seq<i32>, x: int, upto: int, last_lt: int) -> Seq<i32>
    decreases upto,
{
    if upto <= 0 {
        seq![]
    } else {
        spec_pivot_coloring(d, x, upto - 1, last_lt).push(spec_pivot_color(d, x, upto - 1, last_lt))
    }
}

proof fn lemma_pivot_coloring_props(d: Seq<i32>, x: int, upto: int, last_lt: int)
    requires
        0 <= upto <= d.len(),
    ensures
        spec_pivot_coloring(d, x, upto, last_lt).len() == upto,
        forall|k: int| 0 <= k < upto ==>
            #[trigger] spec_pivot_coloring(d, x, upto, last_lt)[k] == spec_pivot_color(d, x, k, last_lt),
    decreases upto,
{
    if upto > 0 {
        lemma_pivot_coloring_props(d, x, upto - 1, last_lt);
    }
}

proof fn lemma_pivot_coloring_valid(d: Seq<i32>, c: Seq<i32>)
    requires
        spec_valid_coloring(d, c),
        forall|k: int| 0 <= k < d.len() ==> 0 <= #[trigger] d[k] as int <= 9,
    ensures
        ({
            let n = d.len() as int;
            let x = spec_threshold(d, c);
            let last_lt = spec_last_lt(d, x, n);
            let pc = spec_pivot_coloring(d, x, n, last_lt);
            spec_valid_coloring(d, pc) && 0 <= x <= 9
        }),
{
    let n = d.len() as int;
    let x = spec_threshold(d, c);
    lemma_threshold_compat(d, c);
    let last_lt = spec_last_lt(d, x, n);
    lemma_last_lt_props(d, x, n);
    lemma_pivot_coloring_props(d, x, n, last_lt);
    let pc = spec_pivot_coloring(d, x, n, last_lt);

    assert(pc.len() == n);
    assert(forall|k: int| 0 <= k < n ==> #[trigger] pc[k] == spec_pivot_color(d, x, k, last_lt));
    assert(forall|k: int| 0 <= k < n ==> #[trigger] pc[k] == 1 || pc[k] == 2) by {
        assert(forall|k: int| 0 <= k < n ==>
            (spec_pivot_color(d, x, k, last_lt) == 1 || spec_pivot_color(d, x, k, last_lt) == 2));
    };

    assert forall|k: int| 0 <= k < n && pc[k] == 1 implies (d[k] as int) <= x by {
        assert(pc[k] == spec_pivot_color(d, x, k, last_lt));
    };
    assert forall|k: int| 0 <= k < n && pc[k] == 2 implies (d[k] as int) >= x by {
        assert(pc[k] == spec_pivot_color(d, x, k, last_lt));
    };

    lemma_c1_sorted_generic(d, pc, x, last_lt, n, c);
    lemma_c2_sorted_generic(d, pc, x, last_lt, n, c);

    let c1 = spec_c1_values(d, pc, n);
    let c2 = spec_c2_values(d, pc, n);
    assert(c1.len() > 0 && c2.len() > 0 ==> c1.last() as int <= c2.first() as int) by {
        if c1.len() > 0 && c2.len() > 0 {
            lemma_kth_color1_pos_valid(d, pc, n, c1.len() as int - 1);
            let i1 = spec_kth_color1_pos(pc, c1.len() as int - 1, n);
            assert(pc[i1] == 1);
            assert((d[i1] as int) <= x);
            lemma_kth_color2_pos_valid(d, pc, n, 0);
            let i2 = spec_kth_color2_pos(pc, 0, n);
            assert(pc[i2] == 2);
            assert((d[i2] as int) >= x);
            assert(c1.last() == c1[c1.len() as int - 1]);
            assert(c1[c1.len() as int - 1] == d[i1]);
            assert(c2.first() == c2[0]);
            assert(c2[0] == d[i2]);
        }
    };

    lemma_merged_sorted_from_parts(d, pc, n);
    assert(spec_valid_coloring(d, pc));
}

proof fn lemma_c1_sorted_generic(d: Seq<i32>, pc: Seq<i32>, x: int, last_lt: int, n: int, c: Seq<i32>)
    requires
        n == d.len(),
        last_lt == spec_last_lt(d, x, n),
        pc.len() == n,
        c.len() == n,
        spec_valid_coloring(d, c),
        forall|k: int| 0 <= k < n && c[k] == 1 ==> (d[k] as int) <= x,
        forall|k: int| 0 <= k < n && c[k] == 2 ==> (d[k] as int) >= x,
        forall|k: int| 0 <= k < n ==> #[trigger] pc[k] == spec_pivot_color(d, x, k, last_lt),
        forall|k: int| 0 <= k < n && pc[k] == 1 ==> (d[k] as int) <= x,
    ensures
        spec_adjacent_nondecreasing(spec_c1_values(d, pc, n)),
{
    let c1 = spec_c1_values(d, pc, n);
    assert forall|p: int| 0 <= p < c1.len() - 1 implies #[trigger] c1[p] <= c1[p + 1] by {
        lemma_kth_color1_pos_valid(d, pc, n, p);
        lemma_kth_color1_pos_valid(d, pc, n, p + 1);
        let i = spec_kth_color1_pos(pc, p, n);
        let j = spec_kth_color1_pos(pc, p + 1, n);
        assert(i < j) by {
            if i >= j {
                lemma_count_before_monotonic(pc, j, i, 1);
            }
        };
        assert(pc[i] == spec_pivot_color(d, x, i, last_lt));
        assert(pc[j] == spec_pivot_color(d, x, j, last_lt));
        if (d[i] as int) < x {
            if (d[j] as int) < x {
                assert(c[i] != 2) by {
                    if c[i] == 2 {
                        assert((d[i] as int) >= x);
                    }
                }
                assert(c[j] != 2) by {
                    if c[j] == 2 {
                        assert((d[j] as int) >= x);
                    }
                }
                lemma_color1_pair_ordered(d, c, i, j);
                assert((d[i] as int) <= (d[j] as int));
            } else {
                assert((d[j] as int) == x);
                assert((d[i] as int) <= (d[j] as int));
            }
        } else {
            assert((d[i] as int) == x);
            assert(last_lt == d.len() as int || i > last_lt);
            if (d[j] as int) < x {
                lemma_last_lt_props(d, x, n);
                if last_lt == d.len() as int {
                    assert((d[j] as int) >= x);
                    assert(false);
                } else {
                    assert(i > last_lt);
                    if j > last_lt {
                        assert((d[j] as int) >= x);
                        assert(false);
                    } else {
                        assert(j <= last_lt);
                        assert(false);
                    }
                }
            } else {
                assert((d[j] as int) == x);
                assert((d[i] as int) <= (d[j] as int));
            }
        }
    };
}

proof fn lemma_c2_sorted_generic(d: Seq<i32>, pc: Seq<i32>, x: int, last_lt: int, n: int, c: Seq<i32>)
    requires
        n == d.len(),
        last_lt == spec_last_lt(d, x, n),
        pc.len() == n,
        c.len() == n,
        spec_valid_coloring(d, c),
        forall|k: int| 0 <= k < n && c[k] == 1 ==> (d[k] as int) <= x,
        forall|k: int| 0 <= k < n && c[k] == 2 ==> (d[k] as int) >= x,
        forall|k: int| 0 <= k < n ==> #[trigger] pc[k] == spec_pivot_color(d, x, k, last_lt),
        forall|k: int| 0 <= k < n && pc[k] == 1 ==> (d[k] as int) <= x,
        forall|k: int| 0 <= k < n && pc[k] == 2 ==> (d[k] as int) >= x,
    ensures
        spec_adjacent_nondecreasing(spec_c2_values(d, pc, n)),
{
    let c2 = spec_c2_values(d, pc, n);
    assert forall|p: int| 0 <= p < c2.len() - 1 implies #[trigger] c2[p] <= c2[p + 1] by {
        lemma_kth_color2_pos_valid(d, pc, n, p);
        lemma_kth_color2_pos_valid(d, pc, n, p + 1);
        let i = spec_kth_color2_pos(pc, p, n);
        let j = spec_kth_color2_pos(pc, p + 1, n);
        assert(i < j) by {
            if i >= j {
                lemma_count_before_monotonic(pc, j, i, 2);
            }
        };
        assert(pc[i] == spec_pivot_color(d, x, i, last_lt));
        assert(pc[j] == spec_pivot_color(d, x, j, last_lt));
        if (d[i] as int) > x {
            if (d[j] as int) > x {
                assert(c[i] != 1) by {
                    if c[i] == 1 {
                        assert((d[i] as int) <= x);
                    }
                }
                assert(c[j] != 1) by {
                    if c[j] == 1 {
                        assert((d[j] as int) <= x);
                    }
                }
                lemma_color2_pair_ordered(d, c, i, j);
            } else {
                assert((d[j] as int) == x);
                assert(last_lt != d.len() as int && j <= last_lt);
                lemma_last_lt_props(d, x, n);
                assert(0 <= last_lt < n);
                assert((d[last_lt] as int) < x);
                assert(j < last_lt);
                lemma_eqx_before_smaller_forces_color2(d, c, x, j, last_lt);
                assert(c[i] != 1) by {
                    if c[i] == 1 {
                        assert((d[i] as int) <= x);
                    }
                }
                lemma_color2_pair_ordered(d, c, i, j);
                assert((d[i] as int) <= (d[j] as int));
            }
        } else {
            assert((d[i] as int) == x);
        }
    };
}

proof fn lemma_nondecreasing_transitive(s: Seq<i32>, i: int, j: int)
    requires
        spec_adjacent_nondecreasing(s),
        0 <= i <= j < s.len(),
    ensures
        s[i] <= s[j],
    decreases j - i,
{
    if i < j {
        lemma_nondecreasing_transitive(s, i, j - 1);
        assert(s[j - 1] <= s[j]);
    }
}


pub struct Solution;

impl Solution {
    fn merge_valid(digits: &Vec<i32>, colors: &Vec<i32>, n: usize) -> (b: bool)
        requires
            n == digits.len(),
            n == colors.len(),
            1 <= n <= 200_000,
            forall|j: int|
                #![trigger digits[j]]
                0 <= j < n as int ==> 0 <= #[trigger] digits[j] <= 9,
            forall|t: int|
                #![trigger colors[t]]
                0 <= t < n as int ==> #[trigger] colors[t] == 1 || colors[t] == 2,
        ensures
            b == spec_adjacent_nondecreasing(spec_merged_digits(digits@, colors@, n as int)),
    {
        let mut merged: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == digits.len(),
                n == colors.len(),
                digits@.len() == n as int,
                colors@.len() == n as int,
                merged@ == spec_c1_values(digits@, colors@, i as int),
            decreases n - i
        {
            proof {
                assert(i < n);
                assert((i as int) < digits@.len());
                assert((i as int) < colors@.len());
                lemma_spec_c1_step(digits@, colors@, i as int);
            }
            if colors[i] == 1 {
                let ghost om = merged@;
                merged.push(digits[i]);
                proof {
                    assert(i < digits.len());
                    assert(merged@ == om.push(digits@[i as int]));
                    let di = digits@[i as int];
                    let tail = seq![di];
                    assert(merged@ == om + tail);
                    let c1_next = spec_c1_values(digits@, colors@, (i + 1) as int);
                    let c1_cur = spec_c1_values(digits@, colors@, i as int);
                    assert(c1_next == c1_cur + tail);
                    assert(merged@ == spec_c1_values(digits@, colors@, (i + 1) as int));
                }
            } else {
                proof {
                    let a = spec_c1_values(digits@, colors@, (i + 1) as int);
                    let b = spec_c1_values(digits@, colors@, i as int);
                    assert(a == b);
                    assert(merged@ == a);
                }
            }
            i = i + 1;
        }
        proof {
            assert(merged@ == spec_c1_values(digits@, colors@, n as int));
        }
        i = 0;
        while i < n
            invariant
                i <= n,
                n == digits.len(),
                n == colors.len(),
                digits@.len() == n as int,
                colors@.len() == n as int,
                merged@ == spec_c1_values(digits@, colors@, n as int) + spec_c2_values(digits@, colors@, i as int),
            decreases n - i
        {
            proof {
                assert(i < n);
                assert((i as int) < digits@.len());
                lemma_spec_c2_step(digits@, colors@, i as int);
            }
            if colors[i] == 2 {
                let ghost om = merged@;
                merged.push(digits[i]);
                proof {
                    assert(i < digits.len());
                    assert(merged@ == om.push(digits@[i as int]));
                    let di = digits@[i as int];
                    let tail = seq![di];
                    assert(merged@ == om + tail);
                    let c2_next = spec_c2_values(digits@, colors@, (i + 1) as int);
                    let c2_cur = spec_c2_values(digits@, colors@, i as int);
                    assert(c2_next == c2_cur + tail);
                    let left = spec_c1_values(digits@, colors@, n as int) + c2_next;
                    let mid = spec_c1_values(digits@, colors@, n as int) + c2_cur;
                    assert(left == mid + tail);
                    assert(merged@ == left);
                }
            } else {
                proof {
                    let ip1 = (i + 1) as int;
                    let s2a = spec_c2_values(digits@, colors@, ip1);
                    let s2b = spec_c2_values(digits@, colors@, i as int);
                    assert(s2a == s2b);
                    let c1n = spec_c1_values(digits@, colors@, n as int);
                    assert(merged@ == c1n + s2a);
                }
            }
            i = i + 1;
        }
        let mlen: usize = merged.len();
        proof {
            assert(merged@ == spec_merged_digits(digits@, colors@, n as int));
            lemma_lens_add_n(digits@, colors@, n as int);
            assert(mlen as int == n as int);
        }
        i = 0;
        while i + 1 < merged.len()
            invariant
                i + 1 <= merged.len(),
                merged.len() == mlen,
                merged@ == spec_merged_digits(digits@, colors@, n as int),
                forall|t: int| #![trigger merged[t]] 0 <= t < i as int ==> merged[t] <= merged[t + 1],
            decreases mlen - 1 - i
        {
            if merged[i] > merged[i + 1] {
                proof {
                    assert(merged@[i as int] > merged@[i as int + 1]);
                    assert(!spec_adjacent_nondecreasing(merged@));
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            lemma_adjacent_from_prefix(merged@, merged.len() as int);
        }
        true
    }

    fn try_pivot(digits: &Vec<i32>, n: usize, x: i32) -> (r: Vec<i32>)
        requires
            n == digits.len(),
            1 <= n <= 200_000,
            0 <= x <= 9,
            forall|j: int|
                #![trigger digits[j]]
                0 <= j < n as int ==> 0 <= #[trigger] digits[j] <= 9,
        ensures
            r.len() == 0 || r.len() == n,
            r.len() == n ==> spec_valid_coloring(digits@, r@),
            r.len() == 0 ==> !spec_valid_coloring(
                digits@,
                spec_pivot_coloring(digits@, x as int, n as int, spec_last_lt(digits@, x as int, n as int)),
            ),
    {
        let mut last_lt: usize = n;
        let mut i: usize = 0;
        while i < n
            invariant
                n == digits.len(),
                i <= n,
                last_lt <= n,
                last_lt == n || (last_lt as int) < (n as int),
                (last_lt as int) == spec_last_lt(digits@, x as int, i as int),
            decreases n - i
        {
            if digits[i] < x {
                last_lt = i;
            }
            proof {
                assert(spec_last_lt(digits@, x as int, (i + 1) as int) == ({
                    let prev = spec_last_lt(digits@, x as int, i as int);
                    if (digits@[i as int] as int) < x as int { i as int } else { prev }
                }));
            }
            i = i + 1;
        }
        let mut colors: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                colors.len() == j,
            decreases n - j
        {
            colors.push(0);
            j = j + 1;
        }
        i = 0;
        while i < n
            invariant
                n == digits.len(),
                i <= n,
                colors.len() == n,
                (last_lt as int) == spec_last_lt(digits@, x as int, n as int),
                forall|t: int|
                    #![trigger colors[t]]
                    0 <= t < i as int ==> #[trigger] colors[t] == 1 || colors[t] == 2,
                forall|t: int|
                    0 <= t < i as int ==>
                        colors@[t] == spec_pivot_color(digits@, x as int, t, last_lt as int),
            decreases n - i
        {
            let d = digits[i];
            let c = if d < x {
                1
            } else if d > x {
                2
            } else {
                if last_lt != n && i <= last_lt {
                    2
                } else {
                    1
                }
            };
            colors.set(i, c);
            proof {
                assert(c == 1 || c == 2);
                assert(c == spec_pivot_color(digits@, x as int, i as int, last_lt as int));
                assert forall|t: int| 0 <= t < i as int implies
                    colors@[t] == spec_pivot_color(digits@, x as int, t, last_lt as int) by {
                }
            }
            i = i + 1;
        }
        proof {
            assert(forall|t: int| 0 <= t < n as int ==> colors@[t] == 1 || colors@[t] == 2);
            assert(forall|t: int| 0 <= t < n as int ==>
                colors@[t] == spec_pivot_color(digits@, x as int, t, last_lt as int));
            assert((last_lt as int) == spec_last_lt(digits@, x as int, n as int));
            lemma_pivot_coloring_props(digits@, x as int, n as int, last_lt as int);
            assert(colors@ =~= spec_pivot_coloring(digits@, x as int, n as int, last_lt as int));
        }
        if Solution::merge_valid(digits, &colors, n) {
            proof {
                assert(spec_adjacent_nondecreasing(spec_merged_digits(digits@, colors@, n as int)));
                assert(spec_valid_coloring(digits@, colors@));
            }
            colors
        } else {
            proof {
                assert(!spec_adjacent_nondecreasing(spec_merged_digits(digits@, colors@, n as int)));
                assert(!spec_valid_coloring(digits@, colors@));
                assert(!spec_valid_coloring(
                    digits@,
                    spec_pivot_coloring(digits@, x as int, n as int, spec_last_lt(digits@, x as int, n as int)),
                ));
            }
            vec![]
        }
    }

    pub fn paint_digits(digits: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= digits.len() <= 200_000,
            forall|i: int|
                #![trigger digits[i]]
                0 <= i < digits.len() as int ==> 0 <= #[trigger] digits[i] <= 9,
        ensures
            res.len() == 0 || res.len() == digits.len(),
            res.len() == digits.len() ==> spec_valid_coloring(digits@, res@),
            res.len() == 0 ==> !spec_exists_valid_coloring(digits@),
    {
        let n = digits.len();
        let mut x: i32 = 0;
        while x <= 9
            invariant
                0 <= x <= 10,
                n == digits.len(),
                1 <= n <= 200_000,
                forall|j: int|
                    #![trigger digits[j]]
                    0 <= j < n as int ==> 0 <= #[trigger] digits[j] <= 9,
                forall|x0: int| 0 <= x0 < x as int ==> !spec_valid_coloring(
                    digits@,
                    spec_pivot_coloring(digits@, x0, n as int, spec_last_lt(digits@, x0, n as int)),
                ),
            decreases 10 - x
        {
            let cand = Solution::try_pivot(&digits, n, x);
            if cand.len() == n {
                proof {
                    assert(spec_valid_coloring(digits@, cand@));
                }
                return cand;
            }
            x = x + 1;
        }
        proof {
            if spec_exists_valid_coloring(digits@) {
                let c = choose|c: Seq<i32>| spec_valid_coloring(digits@, c);
                lemma_pivot_coloring_valid(digits@, c);
                let xt = spec_threshold(digits@, c);
                assert(0 <= xt <= 9);
                assert(spec_valid_coloring(
                    digits@,
                    spec_pivot_coloring(digits@, xt, n as int, spec_last_lt(digits@, xt, n as int)),
                ));
                assert(!spec_valid_coloring(
                    digits@,
                    spec_pivot_coloring(digits@, xt, n as int, spec_last_lt(digits@, xt, n as int)),
                ));
                assert(false);
            }
        }
        vec![]
    }
}

}
