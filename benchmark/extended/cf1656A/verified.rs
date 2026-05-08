use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs_i(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

pub open spec fn spec_good_pair_at_k(s: Seq<i64>, i1: int, j1: int, k: int) -> bool {
    let vi = s[i1 - 1] as int;
    let vj = s[j1 - 1] as int;
    let vk = s[k - 1] as int;
    spec_abs_i(vi - vk) + spec_abs_i(vk - vj) == spec_abs_i(vi - vj)
}

proof fn lemma_abs_sum_ordered(lo: int, mid: int, hi: int)
    requires
        lo <= mid,
        mid <= hi,
    ensures
        spec_abs_i(lo - mid) + spec_abs_i(mid - hi) == spec_abs_i(lo - hi),
{
    assert(lo - mid <= 0);
    assert(spec_abs_i(lo - mid) == mid - lo);
    assert(mid - hi <= 0);
    assert(spec_abs_i(mid - hi) == hi - mid);
    assert(lo - hi <= 0);
    assert(spec_abs_i(lo - hi) == hi - lo);
    assert((mid - lo) + (hi - mid) == hi - lo);
}

proof fn lemma_good_pair_bracketed(
    s: Seq<i64>,
    i1: int,
    j1: int,
    k: int,
    vi: int,
    vj: int,
    vk: int,
)
    requires
        1 <= i1 <= s.len(),
        1 <= j1 <= s.len(),
        1 <= k <= s.len(),
        vi == s[i1 - 1] as int,
        vj == s[j1 - 1] as int,
        vk == s[k - 1] as int,
        vi <= vj,
        vi <= vk,
        vk <= vj,
    ensures
        spec_good_pair_at_k(s, i1, j1, k),
{
    lemma_abs_sum_ordered(vi, vk, vj);
}

proof fn lemma_forall_good_pair_from_extrema(
    s: Seq<i64>,
    im: int,
    ix: int,
    n: int,
)
    requires
        n == s.len(),
        1 <= n,
        0 <= im < n,
        0 <= ix < n,
        forall|t: int| 0 <= t < n ==> (s[im] as int) <= (#[trigger] s[t] as int),
        forall|t: int| 0 <= t < n ==> (s[ix] as int) >= (#[trigger] s[t] as int),
    ensures
        forall|k: int|
            1 <= k <= n ==> #[trigger] spec_good_pair_at_k(s, im + 1, ix + 1, k),
{
    assert forall|k: int|
        1 <= k <= n implies #[trigger] spec_good_pair_at_k(s, im + 1, ix + 1, k) by {
        let vk = s[k - 1] as int;
        let vi = s[im] as int;
        let vj = s[ix] as int;
        assert(vi <= vk);
        assert(vk <= vj);
        assert(vi <= vj);
        lemma_good_pair_bracketed(s, im + 1, ix + 1, k, vi, vj, vk);
    };
}

proof fn lemma_min_prefix_extend(
    s: Seq<i64>,
    prev_min: int,
    i: int,
    new_min: int,
)
    requires
        0 <= prev_min < i,
        i < s.len(),
        forall|t: int| 0 <= t < i ==> (s[prev_min] as int) <= (#[trigger] s[t] as int),
        new_min == if (s[i] as int) < (s[prev_min] as int) {
            i
        } else {
            prev_min
        },
    ensures
        forall|t: int| 0 <= t < i + 1 ==> (s[new_min] as int) <= (#[trigger] s[t] as int),
{
    assert forall|t: int| 0 <= t < i + 1 implies (s[new_min] as int) <= s[t] as int by {
        if t < i {
            if (s[i] as int) < (s[prev_min] as int) {
                assert(new_min == i);
                assert((s[new_min] as int) <= (s[prev_min] as int));
                assert((s[prev_min] as int) <= s[t] as int);
            } else {
                assert(new_min == prev_min);
                assert((s[new_min] as int) <= s[t] as int);
            }
        } else {
            assert(t == i);
            if (s[i] as int) < (s[prev_min] as int) {
                assert(new_min == i);
                assert((s[new_min] as int) <= s[t] as int);
            } else {
                assert(new_min == prev_min);
                assert((s[prev_min] as int) <= (s[i] as int));
                assert((s[new_min] as int) <= s[t] as int);
            }
        }
    };
}

proof fn lemma_max_prefix_extend(
    s: Seq<i64>,
    prev_max: int,
    i: int,
    new_max: int,
)
    requires
        0 <= prev_max < i,
        i < s.len(),
        forall|t: int| 0 <= t < i ==> (s[prev_max] as int) >= (#[trigger] s[t] as int),
        new_max == if (s[i] as int) > (s[prev_max] as int) {
            i
        } else {
            prev_max
        },
    ensures
        forall|t: int| 0 <= t < i + 1 ==> (s[new_max] as int) >= (#[trigger] s[t] as int),
{
    assert forall|t: int| 0 <= t < i + 1 implies (s[new_max] as int) >= s[t] as int by {
        if t < i {
            if (s[i] as int) > (s[prev_max] as int) {
                assert(new_max == i);
                assert((s[prev_max] as int) >= s[t] as int);
                assert((s[i] as int) >= (s[prev_max] as int));
            } else {
                assert(new_max == prev_max);
                assert((s[new_max] as int) >= s[t] as int);
            }
        } else {
            assert(t == i);
            if (s[i] as int) > (s[prev_max] as int) {
                assert(new_max == i);
                assert((s[new_max] as int) >= s[t] as int);
            } else {
                assert(new_max == prev_max);
                assert((s[i] as int) <= (s[prev_max] as int));
                assert((s[new_max] as int) >= s[t] as int);
            }
        }
    };
}

impl Solution {
    pub fn good_pair_indices(a: Vec<i64>) -> (res: (i64, i64))
        requires
            1 <= a.len() <= 200_000,
            forall|t: int| 0 <= t < a.len() ==> #[trigger] (a[t] as int) >= 1,
        ensures
            1 <= res.0 as int <= a.len() as int,
            1 <= res.1 as int <= a.len() as int,
            forall|k: int|
                1 <= k <= a.len() ==> #[trigger] spec_good_pair_at_k(a@, res.0 as int, res.1 as int, k),
    {
        let ghost seq0 = a@;
        let n = a.len();
        let mut min_i = 0usize;
        let mut max_i = 0usize;
        let mut i = 1usize;
        while i < n
            invariant
                seq0 == a@,
                n == a.len(),
                1 <= n <= 200_000,
                forall|t: int| 0 <= t < a.len() ==> #[trigger] (a[t] as int) >= 1,
                1 <= i <= n,
                0 <= min_i < i,
                0 <= max_i < i,
                forall|t: int| 0 <= t < i ==> (seq0[min_i as int] as int) <= (#[trigger] seq0[t] as int),
                forall|t: int| 0 <= t < i ==> (seq0[max_i as int] as int) >= (#[trigger] seq0[t] as int),
            decreases n - i,
        {
            proof {
                assert(0 <= i as int && (i as int) < (n as int));
                assert(seq0 == a@);
            }
            let ghost prev_min = min_i as int;
            let ghost prev_max = max_i as int;
            if a[i] < a[min_i] {
                min_i = i;
            }
            if a[i] > a[max_i] {
                max_i = i;
            }
            proof {
                let new_min = min_i as int;
                let new_max = max_i as int;
                assert(new_min == if (seq0[i as int] as int) < (seq0[prev_min] as int) {
                    i as int
                } else {
                    prev_min
                });
                lemma_min_prefix_extend(seq0, prev_min, i as int, new_min);
                assert(new_max == if (seq0[i as int] as int) > (seq0[prev_max] as int) {
                    i as int
                } else {
                    prev_max
                });
                lemma_max_prefix_extend(seq0, prev_max, i as int, new_max);
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(0 <= min_i < n);
            assert(0 <= max_i < n);
            assert(1 <= (min_i + 1) as int && (min_i + 1) as int <= n as int);
            assert(1 <= (max_i + 1) as int && (max_i + 1) as int <= n as int);
            lemma_forall_good_pair_from_extrema(seq0, min_i as int, max_i as int, n as int);
            assert forall|k: int|
                1 <= k <= a.len() implies #[trigger] spec_good_pair_at_k(
                    a@,
                    (min_i + 1) as int,
                    (max_i + 1) as int,
                    k,
                ) by {
                assert(a@ == seq0);
            };
        }
        ((min_i + 1) as i64, (max_i + 1) as i64)
    }
}

}
