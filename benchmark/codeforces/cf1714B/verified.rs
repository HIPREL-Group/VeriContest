use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn suffix_pairwise_distinct(s: Seq<i32>, lo: int, hi: int) -> bool {
    forall|i: int|
        #![trigger s[i]]
        lo <= i && i < hi ==> forall|j: int|
            #![trigger s[j]]
            i < j && j < hi ==> s[i] != s[j]
}

pub open spec fn value_appears_in_range(s: Seq<i32>, val: int, lo: int, hi: int) -> bool {
    exists|idx: int| lo <= idx && idx < hi && #[trigger] s[idx] as int == val
}

proof fn lemma_suffix_empty(s: Seq<i32>, lo: int, hi: int)
    requires
        lo == hi,
    ensures
        suffix_pairwise_distinct(s, lo, hi),
{
}

proof fn lemma_suffix_extend(s: Seq<i32>, i: int, n: int)
    requires
        0 < i <= n,
        s.len() == n,
        suffix_pairwise_distinct(s, i, n),
        !value_appears_in_range(s, s[i - 1] as int, i, n),
    ensures
        suffix_pairwise_distinct(s, i - 1, n),
{
    assert forall|p: int, q: int|
        i - 1 <= p && p < q && q < n implies s[p] != s[q] by {
        if i - 1 <= p && p < q && q < n {
            if p == i - 1 {
                assert(q >= i);
                assert(s[i - 1] != s[q]);
                assert(!value_appears_in_range(s, s[i - 1] as int, i, n));
                if s[q] as int == s[i - 1] as int {
                    assert(value_appears_in_range(s, s[i - 1] as int, i, n));
                }
            } else {
                assert(i <= p);
                assert(suffix_pairwise_distinct(s, i, n));
                assert(s[p] != s[q]);
            }
        }
    };
}

proof fn lemma_dup_pair_makes_bad(s: Seq<i32>, k: int, n: int, p: int, q: int)
    requires
        s.len() == n,
        k <= p,
        p < q,
        q < n,
        s[p] == s[q],
    ensures
        !suffix_pairwise_distinct(s, k, n),
{
    assert(p < q && q < n);
    assert(s[p] == s[q]);
    assert(!suffix_pairwise_distinct(s, k, n));
}

proof fn lemma_v_ne_x_range_equiv(s: Seq<i32>, v: int, x: int, i_old: int, n: int)
    requires
        s.len() == n,
        0 < i_old <= n,
        v != x,
        s[i_old - 1] as int == x,
    ensures
        value_appears_in_range(s, v, i_old - 1, n) == value_appears_in_range(s, v, i_old, n),
{
    assert((value_appears_in_range(s, v, i_old - 1, n) ==> value_appears_in_range(s, v, i_old, n))) by {
        if value_appears_in_range(s, v, i_old - 1, n) {
            let idx0 = choose|idx: int|
                i_old - 1 <= idx && idx < n && #[trigger] s[idx] as int == v;
            if idx0 == i_old - 1 {
                assert(s[idx0] as int == x);
                assert(false);
            } else {
                assert(i_old <= idx0);
                assert(value_appears_in_range(s, v, i_old, n));
            }
        }
    };
    assert((value_appears_in_range(s, v, i_old, n) ==> value_appears_in_range(s, v, i_old - 1, n))) by {
        if value_appears_in_range(s, v, i_old, n) {
            let idx1 = choose|idx: int|
                i_old <= idx && idx < n && #[trigger] s[idx] as int == v;
            assert(i_old - 1 <= idx1);
            assert(value_appears_in_range(s, v, i_old - 1, n));
        }
    };
    assert(value_appears_in_range(s, v, i_old - 1, n) == value_appears_in_range(s, v, i_old, n));
}

proof fn lemma_invariant_after_step(
    s: Seq<i32>,
    old_seen: Seq<bool>,
    new_seen: Seq<bool>,
    i_old: int,
    n: int,
    x: int,
)
    requires
        s.len() == n,
        0 < i_old <= n,
        1 <= x && x <= n,
        forall|v: int|
            #![trigger old_seen[v]]
            1 <= v && v <= n ==> old_seen[v] == value_appears_in_range(s, v, i_old, n),
        new_seen[x as int] == true,
        forall|v: int|
            #![trigger old_seen[v]]
            1 <= v && v <= n && v != x ==> new_seen[v] == old_seen[v],
        s[i_old - 1] as int == x,
        !old_seen[x],
    ensures
        forall|v: int|
            #![trigger new_seen[v]]
            1 <= v && v <= n ==> new_seen[v] == value_appears_in_range(s, v, i_old - 1, n),
{
    assert forall|v: int| 1 <= v && v <= n implies new_seen[v] == value_appears_in_range(s, v, i_old - 1, n) by {
        if v == x {
            assert(new_seen[v] == true);
            assert(value_appears_in_range(s, v, i_old - 1, n));
        } else {
            assert(new_seen[v] == old_seen[v]);
            lemma_v_ne_x_range_equiv(s, v, x, i_old, n);
            assert(old_seen[v] == value_appears_in_range(s, v, i_old, n));
            assert(new_seen[v] == value_appears_in_range(s, v, i_old - 1, n));
        }
    };
}

pub struct Solution;

impl Solution {
    pub fn min_prefix_removals(n: usize, a: Vec<i32>) -> (result: usize)
        requires
            n >= 1,
            (n as int) <= 200_000,
            a.len() == n,
            forall|i: int|
                #![trigger a[i]]
                0 <= i && i < n as int ==> 1 <= a[i] as int && a[i] as int <= n as int,
        ensures
            0 <= result <= n,
            suffix_pairwise_distinct(a@, result as int, n as int),
            forall|k: int|
                #![trigger suffix_pairwise_distinct(a@, k, n as int)]
                0 <= k && k < result as int ==> !suffix_pairwise_distinct(a@, k, n as int),
    {
        proof {
            assert((n as int) + 1 <= 200_001) by (nonlinear_arith)
                requires
                    (n as int) <= 200_000;
        }
        let mut seen: Vec<bool> = Vec::new();
        let mut j: usize = 0;
        while j <= n
            invariant
                seen.len() == j,
                j <= n + 1,
                (n as int) <= 200_000,
                forall|kk: int|
                    #![trigger seen[kk]]
                    0 <= kk && kk < seen.len() as int ==> seen[kk] == false,
            decreases n + 1 - j,
        {
            proof {
                assert(j <= n);
                assert((j as int) + 1 <= (n as int) + 1);
                assert((n as int) + 1 <= 200_001) by (nonlinear_arith)
                    requires
                        (n as int) <= 200_000;
            }
            seen.push(false);
            j = j + 1;
        }
        proof {
            lemma_suffix_empty(a@, n as int, n as int);
            assert forall|v: int|
                #![trigger seen[v]]
                1 <= v && v <= n as int implies seen@[v] == value_appears_in_range(a@, v, n as int, n as int) by {
                assert(seen@[v] == false);
                assert(!value_appears_in_range(a@, v, n as int, n as int));
            };
        }
        let mut i: usize = n;
        while i > 0
            invariant
                a.len() == n,
                seen.len() == n + 1,
                0 <= i && i <= n,
                forall|ii: int|
                    #![trigger a[ii]]
                    0 <= ii && ii < n as int ==> 1 <= a[ii] as int && a[ii] as int <= n as int,
                suffix_pairwise_distinct(a@, i as int, n as int),
                forall|v: int|
                    #![trigger seen[v]]
                    1 <= v && v <= n as int ==> seen[v] == value_appears_in_range(a@, v, i as int, n as int),
            decreases i,
        {
            let x: usize = a[i - 1] as usize;
            proof {
                assert(1 <= x && x <= n);
            }
            if seen[x] {
                proof {
                    assert(suffix_pairwise_distinct(a@, i as int, n as int));
                    assert(seen[x as int]);
                    assert(value_appears_in_range(a@, a[i - 1] as int, i as int, n as int));
                    assert(exists|idx: int|
                        i as int <= idx && idx < n as int && #[trigger] a@[idx] as int == a@[i as int - 1] as int);
                    let jdup = choose|jd: int|
                        i as int <= jd && jd < n as int && #[trigger] a@[jd] as int == a@[i as int - 1] as int;
                    assert(i as int - 1 < jdup);
                    assert(a@[i as int - 1] == a@[jdup]);
                    lemma_dup_pair_makes_bad(a@, i as int - 1, n as int, i as int - 1, jdup);
                    assert forall|k: int|
                        0 <= k && k < i as int implies !suffix_pairwise_distinct(a@, k, n as int) by {
                        assert(k <= i as int - 1);
                        lemma_dup_pair_makes_bad(a@, k, n as int, i as int - 1, jdup);
                    };
                }
                return i;
            }
            proof {
                assert(!seen[x as int]);
                assert(!value_appears_in_range(a@, a[i - 1] as int, i as int, n as int));
                lemma_suffix_extend(a@, i as int, n as int);
            }
            let ghost i_was = i;
            let ghost old_seen = seen@;
            seen.set(x, true);
            i = i - 1;
            proof {
                assert(seen@[x as int] == true);
                assert forall|v: int|
                    1 <= v && v <= n as int && v != x as int implies seen@[v] == old_seen[v] by {
                    assert(seen@[v] == old_seen[v]);
                };
                lemma_invariant_after_step(
                    a@,
                    old_seen,
                    seen@,
                    i_was as int,
                    n as int,
                    x as int,
                );
                assert(suffix_pairwise_distinct(a@, i as int, n as int));
            }
        }
        proof {
            assert(i == 0);
            assert(suffix_pairwise_distinct(a@, 0int, n as int));
            assert forall|k: int|
                0 <= k && k < 0int implies !suffix_pairwise_distinct(a@, k, n as int) by {
                assert(false);
            };
        }
        i
    }
}

}
