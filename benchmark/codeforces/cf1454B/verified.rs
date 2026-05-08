use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn bid_count_upto(a: Seq<i32>, upto: int, v: int) -> int
    decreases upto,
{
    if upto <= 0 {
        0int
    } else {
        (if a[upto - 1] as int == v { 1int } else { 0int }) + bid_count_upto(a, upto - 1, v)
    }
}

pub open spec fn bid_count(a: Seq<i32>, v: int) -> int {
    bid_count_upto(a, a.len() as int, v)
}

proof fn lemma_bid_count_upto_step(a: Seq<i32>, upto: int, v: int)
    requires
        0 < upto <= a.len(),
    ensures
        bid_count_upto(a, upto, v) == bid_count_upto(a, upto - 1, v) + (if a[upto - 1] as int == v {
            1int
        } else {
            0int
        }),
{
}

proof fn lemma_bid_count_upto_le_upto(a: Seq<i32>, upto: int, v: int)
    requires
        0 <= upto <= a.len(),
    ensures
        bid_count_upto(a, upto, v) <= upto,
    decreases upto,
{
    if upto == 0 {
    } else {
        lemma_bid_count_upto_le_upto(a, upto - 1, v);
        assert(bid_count_upto(a, upto, v) == bid_count_upto(a, upto - 1, v) + (if a[upto - 1] as int == v {
            1int
        } else {
            0int
        }));
        assert(bid_count_upto(a, upto - 1, v) <= upto - 1);
        assert(bid_count_upto(a, upto, v) <= upto);
    }
}

proof fn lemma_subrange_prefix_eq(a: Seq<i32>, hi: int)
    requires
        0 < hi <= a.len(),
    ensures
        a.subrange(0, hi).subrange(0, hi - 1) =~= a.subrange(0, hi - 1),
{
    assert forall|k: int|
        0 <= k < hi - 1 implies #[trigger] a.subrange(0, hi).subrange(0, hi - 1)[k] == a.subrange(0, hi - 1)[k] by {
        assert(a.subrange(0, hi).subrange(0, hi - 1)[k] == a[k]);
        assert(a.subrange(0, hi - 1)[k] == a[k]);
    }
}

proof fn lemma_bid_count_upto_subrange_prefix(a: Seq<i32>, hi: int, k: int, v: int)
    requires
        0 <= k <= hi <= a.len(),
    ensures
        bid_count_upto(a, k, v) == bid_count_upto(a.subrange(0, hi), k, v),
    decreases k,
{
    if k == 0 {
    } else {
        lemma_bid_count_upto_subrange_prefix(a, hi, k - 1, v);
        assert(a[k - 1] == a.subrange(0, hi)[k - 1]);
        lemma_bid_count_upto_step(a, k, v);
        lemma_bid_count_upto_step(a.subrange(0, hi), k, v);
    }
}

proof fn lemma_bid_count_upto_seq_agree(s1: Seq<i32>, s2: Seq<i32>, k: int, v: int)
    requires
        0 <= k <= s1.len(),
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() ==> #[trigger] s1[i] == s2[i],
    ensures
        bid_count_upto(s1, k, v) == bid_count_upto(s2, k, v),
    decreases k,
{
    if k == 0 {
    } else {
        lemma_bid_count_upto_seq_agree(s1, s2, k - 1, v);
        lemma_bid_count_upto_step(s1, k, v);
        lemma_bid_count_upto_step(s2, k, v);
        assert(s1[k - 1] == s2[k - 1]);
    }
}

proof fn lemma_bid_count_upto_prefix_match(a: Seq<i32>, upto: int, v: int)
    requires
        0 <= upto <= a.len(),
    ensures
        bid_count_upto(a, upto, v) == bid_count_upto(a.subrange(0, upto), upto, v),
    decreases upto,
{
    if upto == 0 {
    } else {
        lemma_bid_count_upto_prefix_match(a, upto - 1, v);
        lemma_subrange_prefix_eq(a, upto);
        let s1 = a.subrange(0, upto).subrange(0, upto - 1);
        let s2 = a.subrange(0, upto - 1);
        assert(s1 =~= s2);
        lemma_bid_count_upto_subrange_prefix(a.subrange(0, upto), upto - 1, upto - 1, v);
        assert(bid_count_upto(a.subrange(0, upto), upto - 1, v) == bid_count_upto(s1, upto - 1, v));
        lemma_bid_count_upto_seq_agree(s1, s2, upto - 1, v);
        assert(bid_count_upto(s1, upto - 1, v) == bid_count_upto(s2, upto - 1, v));
        assert(bid_count_upto(a.subrange(0, upto - 1), upto - 1, v) == bid_count_upto(a, upto - 1, v)) by {
            lemma_bid_count_upto_prefix_match(a, upto - 1, v);
            assert(bid_count_upto(a, upto - 1, v) == bid_count_upto(a.subrange(0, upto - 1), upto - 1, v));
        }
        assert(a.subrange(0, upto)[upto - 1] == a[upto - 1]);
        assert(bid_count_upto(a, upto, v) == bid_count_upto(a, upto - 1, v) + (if a[upto - 1] as int == v {
            1int
        } else {
            0int
        }));
        assert(bid_count_upto(a.subrange(0, upto), upto, v) == bid_count_upto(a.subrange(0, upto), upto - 1, v) + (if a.subrange(0, upto)[upto - 1] as int == v {
            1int
        } else {
            0int
        }));
    }
}

proof fn lemma_exists_index_for_value(a: Seq<i32>, val: int, n_bound: int)
    requires
        0 < a.len(),
        1 <= val && val <= n_bound,
        forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] && a[k] <= n_bound,
        bid_count(a, val) == 1,
    ensures
        exists|k: int| 0 <= k < a.len() && a[k] == val,
    decreases a.len(),
{
    reveal_with_fuel(bid_count_upto, 2);
    let len = a.len() as int;
    if len == 1 {
        assert(bid_count_upto(a, 1, val) == 1);
        assert(bid_count_upto(a, 0, val) == 0);
        assert((if a[0] as int == val { 1int } else { 0int }) == 1int);
        assert(a[0] as int == val);
    } else {
        lemma_bid_count_upto_step(a, len, val);
        assert(bid_count_upto(a, len, val) == bid_count_upto(a, len - 1, val) + (if a[len - 1] as int == val {
            1int
        } else {
            0int
        }));
        assert(bid_count_upto(a, len, val) == 1);
        if a[len - 1] as int == val {
            assert(bid_count_upto(a, len - 1, val) == 0);
            assert(0 <= len - 1);
            assert(len - 1 < len);
        } else {
            assert(bid_count_upto(a, len - 1, val) == 1);
            lemma_bid_count_upto_prefix_match(a, len - 1, val);
            assert(bid_count_upto(a.subrange(0, len - 1), len - 1, val) == 1);
            assert(bid_count(a.subrange(0, len - 1), val) == 1);
            assert(forall|k: int|
                0 <= k < a.subrange(0, len - 1).len() ==> 1 <= #[trigger] a.subrange(0, len - 1)[k] && a.subrange(0, len - 1)[k] <= n_bound);
            lemma_exists_index_for_value(a.subrange(0, len - 1), val, n_bound);
        }
    }
}

impl Solution {
    pub fn unique_bid_winner(a: Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= a.len() as int,
        ensures
            result == -1 <==> forall|v: int|
                1 <= v <= a.len() as int ==> #[trigger] bid_count(a@, v) != 1,
            result != -1 ==> (
                1 <= (result as int) && (result as int) <= a.len() as int
                && bid_count(a@, a@[(result - 1) as int] as int) == 1
                && forall|v: int|
                    1 <= v <= a.len() as int && bid_count(a@, v) == 1
                        ==> a@[(result - 1) as int] as int <= v
            ),
    {
        let n = a.len();
        let mut freq: Vec<i32> = Vec::new();
        let mut j = 0usize;
        while j < n + 1
            invariant
                n == a.len(),
                1 <= n <= 200_000,
                forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] && a[k] <= n as int,
                j <= n + 1,
                freq.len() == j,
                forall|t: int| 0 <= t < j ==> #[trigger] freq[t] == 0,
            decreases n + 1 - j,
        {
            freq.push(0i32);
            j += 1;
        }
        let mut i = 0usize;
        while i < n
            invariant
                n == a.len(),
                1 <= n <= 200_000,
                forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] && a[k] <= n as int,
                freq.len() == n + 1,
                i <= n,
                forall|t: int|
                    1 <= t <= n as int ==> #[trigger] freq[t] == bid_count_upto(a@, i as int, t),
                forall|t: int| t == 0 ==> #[trigger] freq[t] == 0,
            decreases n - i,
        {
            let vi = a[i] as usize;
            let oldc = freq[vi];
            let ghost old_freq = freq@;
            proof {
                assert(1 <= a@[i as int] as int && a@[i as int] as int <= n as int);
                assert(1 <= vi && vi <= n);
                assert(oldc == bid_count_upto(a@, i as int, vi as int));
                lemma_bid_count_upto_le_upto(a@, i as int, vi as int);
                assert((oldc as int) <= i as int);
                assert((oldc as int) + 1 <= (n as int) + 1);
            }
            freq.set(vi, oldc + 1);
            proof {
                lemma_bid_count_upto_step(a@, i as int + 1, vi as int);
                assert((oldc + 1) as int == bid_count_upto(a@, i as int, vi as int) + (if a@[i as int] as int == vi as int {
                    1int
                } else {
                    0int
                }));
                assert(a@[i as int] as int == vi as int);
                assert(forall|t: int|
                    1 <= t <= n as int && t != vi as int ==> bid_count_upto(a@, i as int + 1, t) == bid_count_upto(
                        a@,
                        i as int,
                        t,
                    ));
                assert forall|t: int| 1 <= t <= n as int implies freq[t] == bid_count_upto(a@, i as int + 1, t) by {
                    if t == vi as int {
                        assert(freq[t] == (oldc + 1) as int);
                    } else {
                        assert(freq[t] == old_freq[t]);
                        assert(bid_count_upto(a@, i as int + 1, t) == bid_count_upto(a@, i as int, t));
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(forall|t: int|
                1 <= t <= n as int ==> #[trigger] freq[t] == bid_count_upto(a@, n as int, t));
            assert(forall|t: int|
                1 <= t <= n as int ==> bid_count_upto(a@, n as int, t) == #[trigger] bid_count(a@, t));
        }
        let mut found = false;
        let mut min_val = 0i32;
        let mut v = 1usize;
        while v <= n
            invariant
                n == a.len(),
                1 <= n <= 200_000,
                forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] && a[k] <= n as int,
                freq.len() == n + 1,
                forall|t: int|
                    1 <= t <= n as int ==> #[trigger] freq[t] == bid_count(a@, t),
                1 <= v && v <= n + 1,
                found == exists|x: int|
                    1 <= x < v as int && #[trigger] bid_count(a@, x) == 1,
                found ==> (
                    1 <= (min_val as int) && (min_val as int) < v as int
                        && bid_count(a@, min_val as int) == 1
                        && forall|x: int|
                            1 <= x < v as int && bid_count(a@, x) == 1 ==> (min_val as int) <= x
                ),
                !found ==> forall|x: int|
                    1 <= x < v as int ==> #[trigger] bid_count(a@, x) != 1,
            decreases n + 1 - v,
        {
            if freq[v] == 1 {
                if !found || (v as i32) < min_val {
                    min_val = v as i32;
                    found = true;
                }
            }
            proof {
                assert(freq[v as int] == bid_count(a@, v as int));
            }
            v += 1;
        }
        if !found {
            proof {
                assert(v == n + 1);
                assert(!exists|x: int| 1 <= x < v as int && bid_count(a@, x) == 1);
                assert forall|x: int| 1 <= x <= n as int implies bid_count(a@, x) != 1 by {
                    assert(1 <= x && x < v as int);
                }
            }
            return -1;
        }
        proof {
            assert(v == n + 1);
            assert(exists|x: int| 1 <= x < v as int && bid_count(a@, x) == 1);
            assert(1 <= (min_val as int) && (min_val as int) <= n as int);
            assert(bid_count(a@, min_val as int) == 1);
            assert forall|x: int| 1 <= x <= n as int && bid_count(a@, x) == 1 implies (min_val as int) <= x by {
                assert(x < v as int);
            }
            lemma_exists_index_for_value(a@, min_val as int, n as int);
        }
        i = 0usize;
        while i < n
            invariant
                n == a.len(),
                1 <= n <= 200_000,
                forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] && a[k] <= n as int,
                found,
                1 <= (min_val as int) && (min_val as int) <= n as int,
                bid_count(a@, min_val as int) == 1,
                forall|x: int|
                    1 <= x <= n as int && bid_count(a@, x) == 1 ==> (min_val as int) <= x,
                i <= n,
                forall|k: int| 0 <= k < i as int ==> a[k] != min_val,
            decreases n - i,
        {
            if a[i] == min_val {
                proof {
                    assert(0 <= (i as int) && (i as int) < (n as int));
                    assert(bid_count(a@, a@[i as int] as int) == 1);
                    assert forall|t: int|
                        1 <= t <= n as int && bid_count(a@, t) == 1 implies a@[i as int] as int <= t by {
                        assert((min_val as int) <= t);
                        assert(a@[i as int] == min_val);
                    }
                }
                return (i + 1) as i32;
            }
            i += 1;
        }
        proof {
            assert(false);
        }
        -1
    }
}

}
