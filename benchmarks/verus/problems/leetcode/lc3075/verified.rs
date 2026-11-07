use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::relations::*;
use vstd::multiset::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_index_prefix(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            0
        } else {
            let j = Self::max_index_prefix(s, n - 1);
            if s[n - 1] >= s[j] {
                n - 1
            } else {
                j
            }
        }
    }

    pub open spec fn max_value(s: Seq<i32>) -> int {
        if s.len() == 0 {
            -1
        } else {
            s[Self::max_index_prefix(s, s.len() as int)] as int
        }
    }

    pub open spec fn pick_max_mark(s: Seq<i32>) -> Seq<i32> {
        if s.len() == 0 {
            s
        } else {
            s.update(Self::max_index_prefix(s, s.len() as int), -1i32)
        }
    }

    pub open spec fn after_rounds(s: Seq<i32>, rounds: int) -> Seq<i32>
        decreases rounds,
    {
        if rounds <= 0 {
            s
        } else {
            Self::pick_max_mark(Self::after_rounds(s, rounds - 1))
        }
    }

    pub open spec fn clamp_gain(v: int, taken: int) -> int {
        if v - taken > 0 {
            v - taken
        } else {
            0
        }
    }

    pub open spec fn maximum_from_state(s: Seq<i32>, rounds: int, taken: int) -> int
        decreases rounds,
    {
        if rounds <= 0 || s.len() == 0 {
            0
        } else {
            Self::clamp_gain(Self::max_value(s), taken)
                + Self::maximum_from_state(Self::pick_max_mark(s), rounds - 1, taken + 1)
        }
    }

    pub open spec fn maximum_happiness_sum_spec(happiness: Seq<i32>, k: int) -> int {
        Self::maximum_from_state(happiness, k, 0)
    }
}

pub open spec fn desc_leq(a: i32, b: i32) -> bool {
    a >= b
}

proof fn lemma_desc_leq_total_ordering()
    ensures total_ordering(|a: i32, b: i32| desc_leq(a, b)),
{
}

proof fn lemma_max_index_prefix_props(s: Seq<i32>, n: int)
    requires 1 <= n <= s.len(),
    ensures
        0 <= Solution::max_index_prefix(s, n) < n,
        forall |i: int| 0 <= i < n ==> #[trigger] s[i] <= s[Solution::max_index_prefix(s, n)],
    decreases n,
{
    if n > 1 {
        lemma_max_index_prefix_props(s, n - 1);
    }
}

proof fn lemma_max_value_is_max(s: Seq<i32>)
    requires s.len() >= 1,
    ensures
        forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= Solution::max_value(s),
        s.contains(Solution::max_value(s) as i32),
{
    lemma_max_index_prefix_props(s, s.len() as int);
    let j = Solution::max_index_prefix(s, s.len() as int);
    assert(s[j] == Solution::max_value(s));
    assert(s.contains(s[j]));
}

proof fn lemma_max_value_eq_sorted_first(s: Seq<i32>)
    requires s.len() >= 1,
    ensures
        Solution::max_value(s) == s.sort_by(|a: i32, b: i32| desc_leq(a, b))[0] as int,
        s.sort_by(|a: i32, b: i32| desc_leq(a, b)).len() == s.len(),
{
    broadcast use group_to_multiset_ensures;
    lemma_desc_leq_total_ordering();
    let leq = |a: i32, b: i32| desc_leq(a, b);
    s.lemma_sort_by_ensures(leq);
    let sd = s.sort_by(leq);
    assert(sd.to_multiset() =~= s.to_multiset());
    assert(sd.len() == sd.to_multiset().len());
    assert(s.len() == s.to_multiset().len());
    assert(sd.len() == s.len());
    lemma_max_value_is_max(s);
    assert(sd.contains(sd[0]));
    assert(sd.to_multiset().contains(sd[0]));
    assert(s.to_multiset().contains(sd[0]));
    assert(s.contains(sd[0]));
    let i = choose |i: int| 0 <= i < s.len() && s[i] == sd[0];
    assert(s[i] <= Solution::max_value(s));
    assert(sd[0] as int <= Solution::max_value(s));
    assert(s.contains(Solution::max_value(s) as i32));
    let j = choose |j: int| 0 <= j < s.len() && s[j] == Solution::max_value(s) as i32;
    assert(s.to_multiset().contains(s[j]));
    assert(sd.to_multiset().contains(s[j]));
    assert(sd.contains(s[j]));
    let k = choose |k: int| 0 <= k < sd.len() && sd[k] == s[j];
    assert(sorted_by(sd, leq));
    if k > 0 {
        assert(leq(sd[0], sd[k]));
        assert(desc_leq(sd[0], sd[k]));
        assert(sd[0] >= sd[k]);
        assert(sd[0] as int >= Solution::max_value(s));
    }
    assert(Solution::max_value(s) <= sd[0] as int);
}

pub open spec fn sum_clamp_gain(sd: Seq<i32>, rounds: int, taken: int) -> int
    decreases rounds,
{
    if rounds <= 0 {
        0
    } else {
        Solution::clamp_gain(sd[0] as int, taken) + sum_clamp_gain(sd.drop_first(), rounds - 1, taken + 1)
    }
}

proof fn lemma_sum_clamp_gain_push(sd: Seq<i32>, x: i32, rounds: int, taken: int)
    requires 0 <= rounds <= sd.len(),
    ensures sum_clamp_gain(sd.push(x), rounds, taken) == sum_clamp_gain(sd, rounds, taken),
    decreases rounds,
{
    if rounds > 0 {
        assert(sd.push(x)[0] == sd[0]);
        assert(sd.push(x).drop_first() =~= sd.drop_first().push(x));
        lemma_sum_clamp_gain_push(sd.drop_first(), x, rounds - 1, taken + 1);
    }
}

proof fn lemma_pick_max_mark_sorted(s: Seq<i32>)
    requires
        s.len() >= 1,
        forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1 || s[i] == -1,
    ensures {
        let leq = |a: i32, b: i32| desc_leq(a, b);
        let sd = s.sort_by(leq);
        Solution::pick_max_mark(s).sort_by(leq) =~= sd.drop_first().push(-1i32)
    },
{
    broadcast use group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    lemma_desc_leq_total_ordering();
    let leq = |a: i32, b: i32| desc_leq(a, b);
    s.lemma_sort_by_ensures(leq);
    let sd = s.sort_by(leq);
    assert(sd.to_multiset() =~= s.to_multiset());
    assert(sd.len() == sd.to_multiset().len());
    assert(s.len() == s.to_multiset().len());
    assert(sd.len() == s.len());

    lemma_max_index_prefix_props(s, s.len() as int);
    let idx = Solution::max_index_prefix(s, s.len() as int);
    let pm = Solution::pick_max_mark(s);
    assert(pm =~= s.update(idx, -1i32));
    assert(s[idx] as int == Solution::max_value(s));
    lemma_max_value_eq_sorted_first(s);
    assert(s[idx] == sd[0]);

    assert(pm.to_multiset() =~= s.to_multiset().remove(s[idx]).insert(-1i32)) by {
        assert(s.remove(idx).to_multiset() =~= s.to_multiset().remove(s[idx]));
        assert(pm =~= s.remove(idx).insert(idx, -1i32));
        assert(pm.to_multiset() =~= s.remove(idx).to_multiset().insert(-1i32));
    }

    let target = sd.drop_first().push(-1i32);
    assert(sd =~= seq![sd[0]] + sd.drop_first());
    lemma_multiset_commutative(seq![sd[0]], sd.drop_first());
    assert(seq![sd[0]].to_multiset() =~= Multiset::<i32>::empty().insert(sd[0])) by {
        assert(seq![sd[0]] =~= Seq::<i32>::empty().push(sd[0]));
    }
    assert(sd.to_multiset() =~= Multiset::<i32>::empty().insert(sd[0]).add(sd.drop_first().to_multiset()));
    assert(s.to_multiset() =~= Multiset::<i32>::empty().insert(sd[0]).add(sd.drop_first().to_multiset()));
    assert(s.to_multiset().remove(s[idx]) =~= sd.drop_first().to_multiset());
    assert(pm.to_multiset() =~= sd.drop_first().to_multiset().insert(-1i32));
    assert(target =~= sd.drop_first().add(seq![-1i32]));
    assert(target.to_multiset() =~= sd.drop_first().to_multiset().add(seq![-1i32].to_multiset()));
    assert(seq![-1i32].to_multiset() =~= Multiset::<i32>::empty().insert(-1i32));
    assert(pm.to_multiset() =~= target.to_multiset());

    pm.lemma_sort_by_ensures(leq);
    let pm_sorted = pm.sort_by(leq);
    assert(pm_sorted.to_multiset() =~= pm.to_multiset());
    assert(pm_sorted.len() == pm_sorted.to_multiset().len());
    assert(pm.len() == pm.to_multiset().len());
    assert(target.len() == target.to_multiset().len());
    assert(pm_sorted.to_multiset() =~= target.to_multiset());
    assert(pm_sorted.len() == target.len());
    assert(sorted_by(pm_sorted, leq));

    assert(sorted_by(target, leq)) by {
        assert forall |i: int, j: int| 0 <= i < j < target.len() implies #[trigger] leq(target[i], target[j]) by {
            if j < target.len() - 1 {
                assert(target[i] == sd.drop_first()[i]);
                assert(target[j] == sd.drop_first()[j]);
                assert(sd[i + 1] == sd.drop_first()[i]);
                assert(sd[j + 1] == sd.drop_first()[j]);
                assert(sorted_by(sd, leq));
                assert(leq(sd[i + 1], sd[j + 1]));
            } else {
                assert(target[j] == -1i32);
                if i < target.len() - 1 {
                    assert(target[i] == sd.drop_first()[i]);
                    assert(sd[i + 1] == sd.drop_first()[i]);
                    assert(sd.contains(sd[i + 1]));
                    assert(s.contains(sd[i + 1])) by {
                        assert(sd.to_multiset().contains(sd[i + 1]));
                        assert(s.to_multiset().contains(sd[i + 1]));
                    }
                    let w = choose |w: int| 0 <= w < s.len() && s[w] == sd[i + 1];
                    assert(sd[i + 1] >= 1 || sd[i + 1] == -1);
                    assert(desc_leq(sd[i + 1], -1i32));
                } else {
                }
            }
        }
    }
    lemma_sorted_unique(pm_sorted, target, leq);
}

proof fn lemma_pick_max_mark_preserves_marker_invariant(s: Seq<i32>)
    requires
        s.len() >= 1,
        forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1 || s[i] == -1,
    ensures
        forall |i: int| 0 <= i < s.len() ==>
            #[trigger] Solution::pick_max_mark(s)[i] >= 1 || Solution::pick_max_mark(s)[i] == -1,
        Solution::pick_max_mark(s).len() == s.len(),
{
    lemma_max_index_prefix_props(s, s.len() as int);
}

proof fn lemma_maximum_from_state_eq_sum(s: Seq<i32>, rounds: int, taken: int)
    requires
        0 <= rounds <= s.len(),
        forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1 || s[i] == -1,
    ensures
        Solution::maximum_from_state(s, rounds, taken)
            == sum_clamp_gain(s.sort_by(|a: i32, b: i32| desc_leq(a, b)), rounds, taken),
    decreases rounds,
{
    lemma_desc_leq_total_ordering();
    let leq = |a: i32, b: i32| desc_leq(a, b);
    if rounds > 0 {
        assert(s.len() >= 1);
        lemma_max_value_eq_sorted_first(s);
        let sd = s.sort_by(leq);
        let pm = Solution::pick_max_mark(s);
        lemma_pick_max_mark_sorted(s);
        lemma_pick_max_mark_preserves_marker_invariant(s);
        let pm_sorted = pm.sort_by(leq);
        assert(pm_sorted =~= sd.drop_first().push(-1i32));
        assert(pm.len() == s.len());
        lemma_maximum_from_state_eq_sum(pm, rounds - 1, taken + 1);
        assert(Solution::maximum_from_state(pm, rounds - 1, taken + 1)
            == sum_clamp_gain(pm_sorted, rounds - 1, taken + 1));
        assert(rounds - 1 <= sd.drop_first().len());
        lemma_sum_clamp_gain_push(sd.drop_first(), -1i32, rounds - 1, taken + 1);
        assert(sum_clamp_gain(pm_sorted, rounds - 1, taken + 1) == sum_clamp_gain(sd.drop_first(), rounds - 1, taken + 1));
        assert(sum_clamp_gain(sd, rounds, taken)
            == Solution::clamp_gain(sd[0] as int, taken) + sum_clamp_gain(sd.drop_first(), rounds - 1, taken + 1));
        assert(Solution::max_value(s) == sd[0] as int);
    }
}

proof fn lemma_sum_clamp_gain_split_last(sd: Seq<i32>, rounds: int, taken: int)
    requires 1 <= rounds <= sd.len(),
    ensures sum_clamp_gain(sd, rounds, taken)
        == sum_clamp_gain(sd, rounds - 1, taken) + Solution::clamp_gain(sd[rounds - 1] as int, taken + rounds - 1),
    decreases rounds,
{
    if rounds == 1 {
        assert(sum_clamp_gain(sd, 1, taken)
            == Solution::clamp_gain(sd[0] as int, taken) + sum_clamp_gain(sd.drop_first(), 0, taken + 1));
        assert(sum_clamp_gain(sd.drop_first(), 0, taken + 1) == 0);
        assert(sum_clamp_gain(sd, 0, taken) == 0);
    } else {
        lemma_sum_clamp_gain_split_last(sd.drop_first(), rounds - 1, taken + 1);
        assert(sd.drop_first()[rounds - 2] == sd[rounds - 1]);
        assert(sum_clamp_gain(sd.drop_first(), rounds - 1, taken + 1)
            == sum_clamp_gain(sd.drop_first(), rounds - 2, taken + 1)
                + Solution::clamp_gain(sd.drop_first()[rounds - 2] as int, taken + 1 + rounds - 2));
        assert(sum_clamp_gain(sd, rounds, taken)
            == Solution::clamp_gain(sd[0] as int, taken) + sum_clamp_gain(sd.drop_first(), rounds - 1, taken + 1));
        assert(sum_clamp_gain(sd, rounds - 1, taken)
            == Solution::clamp_gain(sd[0] as int, taken) + sum_clamp_gain(sd.drop_first(), rounds - 2, taken + 1));
    }
}

pub open spec fn merge_seq_desc(a: Seq<i32>, b: Seq<i32>) -> Seq<i32>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] >= b[0] {
        seq![a[0]] + merge_seq_desc(a.drop_first(), b)
    } else {
        seq![b[0]] + merge_seq_desc(a, b.drop_first())
    }
}

pub open spec fn merge_sort_seq_desc(s: Seq<i32>) -> Seq<i32>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        let mid = s.len() as int / 2;
        merge_seq_desc(merge_sort_seq_desc(s.subrange(0, mid)), merge_sort_seq_desc(s.subrange(mid, s.len() as int)))
    }
}

proof fn lemma_sorted_drop_first_desc(s: Seq<i32>)
    requires sorted_by(s, |a: i32, b: i32| desc_leq(a, b)), s.len() >= 1,
    ensures sorted_by(s.drop_first(), |a: i32, b: i32| desc_leq(a, b)),
{
    let leq = |a: i32, b: i32| desc_leq(a, b);
    assert forall |i: int, j: int| 0 <= i < j < s.drop_first().len() implies
        #[trigger] leq(s.drop_first()[i], s.drop_first()[j]) by {
        assert(s.drop_first()[i] == s[i + 1]);
        assert(s.drop_first()[j] == s[j + 1]);
        assert(leq(s[i + 1], s[j + 1]));
    }
}

proof fn lemma_sorted_cons_desc(x: i32, rest: Seq<i32>)
    requires sorted_by(rest, |a: i32, b: i32| desc_leq(a, b)), rest.len() == 0 || x >= rest[0],
    ensures sorted_by(seq![x] + rest, |a: i32, b: i32| desc_leq(a, b)),
{
    let leq = |a: i32, b: i32| desc_leq(a, b);
    assert forall |i: int, j: int| 0 <= i < j < (seq![x] + rest).len() implies
        #[trigger] leq((seq![x] + rest)[i], (seq![x] + rest)[j]) by {
        if i == 0 {
            if j == 1 {
            } else {
                assert((seq![x] + rest)[j] == rest[j - 1]);
                assert(leq(rest[0], rest[j - 1]));
            }
        } else {
            assert((seq![x] + rest)[i] == rest[i - 1]);
            assert((seq![x] + rest)[j] == rest[j - 1]);
            assert(leq(rest[i - 1], rest[j - 1]));
        }
    }
}

proof fn lemma_merge_seq_desc_sorted(a: Seq<i32>, b: Seq<i32>)
    requires
        sorted_by(a, |x: i32, y: i32| desc_leq(x, y)),
        sorted_by(b, |x: i32, y: i32| desc_leq(x, y)),
    ensures sorted_by(merge_seq_desc(a, b), |x: i32, y: i32| desc_leq(x, y)),
    decreases a.len() + b.len(),
{
    let leq = |x: i32, y: i32| desc_leq(x, y);
    if a.len() == 0 || b.len() == 0 {
    } else if a[0] >= b[0] {
        lemma_sorted_drop_first_desc(a);
        lemma_merge_seq_desc_sorted(a.drop_first(), b);
        if merge_seq_desc(a.drop_first(), b).len() > 0 {
            assert(merge_seq_desc(a.drop_first(), b)[0] == a.drop_first()[0] || merge_seq_desc(a.drop_first(), b)[0] == b[0]) by {
                if a.drop_first().len() == 0 {
                    assert(merge_seq_desc(a.drop_first(), b) =~= b);
                } else if b.len() == 0 {
                } else if a.drop_first()[0] >= b[0] {
                } else {
                }
            }
            if a.drop_first().len() > 0 {
                assert(a.drop_first()[0] == a[1]);
                assert(#[trigger] leq(a[0], a[1]));
                assert(a[0] >= a.drop_first()[0]);
            }
            assert(a[0] >= b[0]);
        }
        lemma_sorted_cons_desc(a[0], merge_seq_desc(a.drop_first(), b));
        assert(merge_seq_desc(a, b) =~= seq![a[0]] + merge_seq_desc(a.drop_first(), b));
    } else {
        lemma_sorted_drop_first_desc(b);
        lemma_merge_seq_desc_sorted(a, b.drop_first());
        if merge_seq_desc(a, b.drop_first()).len() > 0 {
            if b.drop_first().len() == 0 {
                assert(merge_seq_desc(a, b.drop_first()) =~= a);
            }
            if b.drop_first().len() > 0 {
                assert(b.drop_first()[0] == b[1]);
                assert(#[trigger] leq(b[0], b[1]));
                assert(b[0] >= b.drop_first()[0]);
            }
            assert(b[0] >= a[0]) by {
                if a.len() == 0 {
                } else {
                }
            }
        }
        lemma_sorted_cons_desc(b[0], merge_seq_desc(a, b.drop_first()));
        assert(merge_seq_desc(a, b) =~= seq![b[0]] + merge_seq_desc(a, b.drop_first()));
    }
}

proof fn lemma_merge_seq_desc_len(a: Seq<i32>, b: Seq<i32>)
    ensures merge_seq_desc(a, b).len() == a.len() + b.len(),
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
    } else if a[0] >= b[0] {
        lemma_merge_seq_desc_len(a.drop_first(), b);
    } else {
        lemma_merge_seq_desc_len(a, b.drop_first());
    }
}

proof fn lemma_merge_seq_desc_multiset(a: Seq<i32>, b: Seq<i32>)
    ensures merge_seq_desc(a, b).to_multiset() =~= a.to_multiset().add(b.to_multiset()),
    decreases a.len() + b.len(),
{
    broadcast use group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    if a.len() == 0 {
        assert(a =~= Seq::<i32>::empty());
    } else if b.len() == 0 {
        assert(b =~= Seq::<i32>::empty());
    } else if a[0] >= b[0] {
        lemma_merge_seq_desc_multiset(a.drop_first(), b);
        assert(merge_seq_desc(a, b) =~= seq![a[0]] + merge_seq_desc(a.drop_first(), b));
        lemma_multiset_commutative(seq![a[0]], merge_seq_desc(a.drop_first(), b));
        assert(a =~= seq![a[0]] + a.drop_first());
        lemma_multiset_commutative(seq![a[0]], a.drop_first());
    } else {
        lemma_merge_seq_desc_multiset(a, b.drop_first());
        assert(merge_seq_desc(a, b) =~= seq![b[0]] + merge_seq_desc(a, b.drop_first()));
        lemma_multiset_commutative(seq![b[0]], merge_seq_desc(a, b.drop_first()));
        assert(b =~= seq![b[0]] + b.drop_first());
        lemma_multiset_commutative(seq![b[0]], b.drop_first());
    }
}

proof fn lemma_merge_sort_seq_desc_sorted(s: Seq<i32>)
    ensures sorted_by(merge_sort_seq_desc(s), |x: i32, y: i32| desc_leq(x, y)),
    decreases s.len(),
{
    if s.len() <= 1 {
        assert forall |i: int, j: int| 0 <= i < j < s.len() implies desc_leq(s[i], s[j]) by {}
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_desc_sorted(s.subrange(0, mid));
        lemma_merge_sort_seq_desc_sorted(s.subrange(mid, s.len() as int));
        lemma_merge_seq_desc_sorted(merge_sort_seq_desc(s.subrange(0, mid)), merge_sort_seq_desc(s.subrange(mid, s.len() as int)));
    }
}

proof fn lemma_merge_sort_seq_desc_len(s: Seq<i32>)
    ensures merge_sort_seq_desc(s).len() == s.len(),
    decreases s.len(),
{
    if s.len() > 1 {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_desc_len(s.subrange(0, mid));
        lemma_merge_sort_seq_desc_len(s.subrange(mid, s.len() as int));
        lemma_merge_seq_desc_len(merge_sort_seq_desc(s.subrange(0, mid)), merge_sort_seq_desc(s.subrange(mid, s.len() as int)));
    }
}

proof fn lemma_merge_sort_seq_desc_multiset(s: Seq<i32>)
    ensures merge_sort_seq_desc(s).to_multiset() =~= s.to_multiset(),
    decreases s.len(),
{
    broadcast use group_to_multiset_ensures;
    if s.len() <= 1 {
    } else {
        let mid = s.len() as int / 2;
        lemma_merge_sort_seq_desc_multiset(s.subrange(0, mid));
        lemma_merge_sort_seq_desc_multiset(s.subrange(mid, s.len() as int));
        lemma_merge_seq_desc_multiset(merge_sort_seq_desc(s.subrange(0, mid)), merge_sort_seq_desc(s.subrange(mid, s.len() as int)));
        assert(s =~= s.subrange(0, mid) + s.subrange(mid, s.len() as int));
        lemma_multiset_commutative(s.subrange(0, mid), s.subrange(mid, s.len() as int));
    }
}

proof fn lemma_merge_sort_seq_desc_eq_sort_by(s: Seq<i32>)
    ensures merge_sort_seq_desc(s) =~= s.sort_by(|a: i32, b: i32| desc_leq(a, b)),
{
    broadcast use group_to_multiset_ensures;
    lemma_desc_leq_total_ordering();
    let leq = |a: i32, b: i32| desc_leq(a, b);
    s.lemma_sort_by_ensures(leq);
    lemma_merge_sort_seq_desc_sorted(s);
    lemma_merge_sort_seq_desc_len(s);
    lemma_merge_sort_seq_desc_multiset(s);
    assert(merge_sort_seq_desc(s).to_multiset() =~= s.sort_by(leq).to_multiset());
    lemma_sorted_unique(merge_sort_seq_desc(s), s.sort_by(leq), leq);
}

fn merge_exec_desc(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        sorted_by(a@, |x: i32, y: i32| desc_leq(x, y)),
        sorted_by(b@, |x: i32, y: i32| desc_leq(x, y)),
    ensures
        result@ =~= merge_seq_desc(a@, b@),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(a@.skip(0) =~= a@);
        assert(b@.skip(0) =~= b@);
    }
    while i < a.len() || j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            result.len() == i + j,
            result@ + merge_seq_desc(a@.skip(i as int), b@.skip(j as int)) =~= merge_seq_desc(a@, b@),
        decreases (a.len() - i) + (b.len() - j),
    {
        if j >= b.len() || (i < a.len() && a[i] >= b[j]) {
            proof {
                assert(a@.skip(i as int)[0] == a@[i as int]);
                assert(a@.skip(i as int).drop_first() =~= a@.skip(i as int + 1));
                if j < b.len() {
                    assert(b@.skip(j as int)[0] == b@[j as int]);
                }
                assert(merge_seq_desc(a@.skip(i as int), b@.skip(j as int))
                    =~= seq![a@[i as int]] + merge_seq_desc(a@.skip(i as int + 1), b@.skip(j as int)));
                assert((result@.push(a@[i as int])) =~= result@ + seq![a@[i as int]]);
            }
            result.push(a[i]);
            i += 1;
        } else {
            proof {
                assert(b@.skip(j as int)[0] == b@[j as int]);
                assert(b@.skip(j as int).drop_first() =~= b@.skip(j as int + 1));
                if i < a.len() {
                    assert(a@.skip(i as int)[0] == a@[i as int]);
                }
                assert(merge_seq_desc(a@.skip(i as int), b@.skip(j as int))
                    =~= seq![b@[j as int]] + merge_seq_desc(a@.skip(i as int), b@.skip(j as int + 1)));
                assert((result@.push(b@[j as int])) =~= result@ + seq![b@[j as int]]);
            }
            result.push(b[j]);
            j += 1;
        }
    }
    proof {
        assert(a@.skip(i as int).len() == 0);
        assert(b@.skip(j as int).len() == 0);
        assert(a@.skip(i as int) =~= Seq::<i32>::empty());
        assert(b@.skip(j as int) =~= Seq::<i32>::empty());
        assert(merge_seq_desc(a@.skip(i as int), b@.skip(j as int)) =~= Seq::<i32>::empty());
        assert(result@ =~= result@ + Seq::<i32>::empty());
    }
    result
}

fn merge_sort_exec_desc(v: &Vec<i32>) -> (result: Vec<i32>)
    requires v.len() <= 200_000,
    ensures result@ =~= merge_sort_seq_desc(v@),
    decreases v.len()
{
    if v.len() <= 1 {
        v.clone()
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
            invariant i <= mid, mid <= v.len(), left@.len() == i as int,
                forall |t: int| 0 <= t < i ==> left@[t] == v@[t],
            decreases mid - i,
        {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut i2: usize = mid;
        while i2 < v.len()
            invariant mid <= i2 <= v.len(), right@.len() == i2 - mid,
                forall |t: int| 0 <= t < i2 - mid ==> right@[t as int] == v@[t + mid as int],
            decreases v.len() - i2,
        {
            right.push(v[i2]);
            i2 += 1;
        }
        proof {
            assert(left@ =~= v@.subrange(0, mid as int));
            assert(right@ =~= v@.subrange(mid as int, v@.len() as int));
        }
        let sorted_left = merge_sort_exec_desc(&left);
        let sorted_right = merge_sort_exec_desc(&right);
        proof {
            lemma_merge_sort_seq_desc_sorted(v@.subrange(0, mid as int));
            lemma_merge_sort_seq_desc_sorted(v@.subrange(mid as int, v@.len() as int));
        }
        let result = merge_exec_desc(&sorted_left, &sorted_right);
        result
    }
}

impl Solution {
    pub fn maximum_happiness_sum(happiness: Vec<i32>, k: i32) -> (result: i64)
        requires
            1 <= happiness.len() <= 200000,
            1 <= k <= happiness.len(),
            forall |i: int| 0 <= i < happiness.len() ==> 1 <= #[trigger] happiness[i] <= 100000000,
        ensures
            result as int == Self::maximum_happiness_sum_spec(happiness@, k as int),
    {
        let sorted = merge_sort_exec_desc(&happiness);
        proof {
            broadcast use group_to_multiset_ensures;
            lemma_desc_leq_total_ordering();
            let leq = |a: i32, b: i32| desc_leq(a, b);
            happiness@.lemma_sort_by_ensures(leq);
            lemma_merge_sort_seq_desc_eq_sort_by(happiness@);
            lemma_merge_sort_seq_desc_len(happiness@);
            assert(sorted@ =~= happiness@.sort_by(leq));
            assert(sorted@.len() == happiness@.len());
            assert forall |t: i32| #[trigger] sorted@.contains(t) implies happiness@.contains(t) by {
                if !happiness@.contains(t) {
                    assert(!sorted@.contains(t));
                }
            }
            assert forall |idx: int| 0 <= idx < sorted@.len() implies
                1 <= #[trigger] sorted@[idx] <= 100000000 by {
                assert(sorted@.contains(sorted@[idx]));
                assert(happiness@.contains(sorted@[idx]));
                let w = choose |w: int| 0 <= w < happiness@.len() && happiness@[w] == sorted@[idx];
            }
            lemma_maximum_from_state_eq_sum(happiness@, k as int, 0);
            assert(Self::maximum_happiness_sum_spec(happiness@, k as int)
                == sum_clamp_gain(sorted@, k as int, 0));
        }
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        let ku = k as usize;
        while i < ku
            invariant
                i <= ku,
                ku == k as usize,
                sorted@.len() == happiness.len(),
                ku <= happiness.len(),
                happiness.len() <= 200000,
                forall |idx: int| 0 <= idx < sorted@.len() ==> 1 <= #[trigger] sorted@[idx] <= 100000000,
                ans as int == sum_clamp_gain(sorted@, i as int, 0),
                0 <= ans <= 100000000 * i as i64,
            decreases ku - i,
        {
            proof {
                assert(1 <= i + 1 <= sorted@.len());
                lemma_sum_clamp_gain_split_last(sorted@, i as int + 1, 0);
                assert(sum_clamp_gain(sorted@, i as int + 1, 0)
                    == sum_clamp_gain(sorted@, i as int, 0)
                        + Solution::clamp_gain(sorted@[i as int] as int, i as int));
            }
            proof {
                assert(i <= 200000);
            }
            let v = sorted[i] as i64;
            let gain = v - i as i64;
            proof {
                assert(v as int == sorted@[i as int] as int);
                assert(gain as int == v as int - i as int);
                assert(Solution::clamp_gain(sorted@[i as int] as int, i as int)
                    == if gain as int > 0 { gain as int } else { 0 });
            }
            proof {
                assert(v <= 100000000);
            }
            if gain > 0 {
                assert(gain <= 100000000) by {
                    assert(v <= 100000000);
                }
                ans = ans + gain;
            }
            i += 1;
        }
        ans
    }
}

}
