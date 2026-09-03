use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn reward_order_sum(reward_values: Seq<i32>, order: Seq<int>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::reward_order_sum(reward_values, order, end - 1)
                + reward_values[order[end - 1]] as int
        }
    }

    pub open spec fn valid_reward_order(reward_values: Seq<i32>, order: Seq<int>) -> bool {
        &&& order.len() <= reward_values.len()
        &&& forall |i: int| 0 <= i < order.len()
            ==> 0 <= #[trigger] order[i] < reward_values.len()
        &&& forall |i: int, j: int| 0 <= i < j < order.len()
            ==> #[trigger] order[i] != #[trigger] order[j]
        &&& forall |i: int| 0 <= i < order.len()
            ==> reward_values[#[trigger] order[i]] as int
                > Self::reward_order_sum(reward_values, order, i)
    }

    pub open spec fn reward_path_ok(reward_values: Seq<i32>, path: Seq<int>) -> bool {
        &&& 1 <= path.len()
        &&& path[0] == 0
        &&& forall |s: int| 0 <= s < path.len() ==> 0 <= #[trigger] path[s] <= 4000
        &&& forall |s: int| 0 <= s < path.len() - 1 ==> exists |i: int|
            0 <= i < reward_values.len()
                && #[trigger] path[s] < #[trigger] reward_values[i] as int
                && path[s + 1] == path[s] + reward_values[i] as int
    }

    pub open spec fn reward_reachable(reward_values: Seq<i32>, total: int) -> bool {
        exists |path: Seq<int>| #[trigger] Self::reward_path_ok(reward_values, path)
            && path[path.len() - 1] == total
    }

    pub open spec fn max_total_reward_spec(reward_values: Seq<i32>, result: int) -> bool {
        &&& 1 <= reward_values.len() <= 2000
        &&& forall |i: int| 0 <= i < reward_values.len() ==> 1 <= #[trigger] reward_values[i] <= 2000
        &&& 0 <= result <= 4000
        &&& Self::reward_reachable(reward_values, result)
        &&& forall |candidate: int| Self::reward_reachable(reward_values, candidate) ==> candidate <= result
    }

    pub proof fn lemma_reachable_zero(reward_values: Seq<i32>)
        ensures
            Self::reward_reachable(reward_values, 0),
    {
        let path: Seq<int> = seq![0];
        assert(Self::reward_path_ok(reward_values, path)) by {
            assert(path.len() == 1);
            assert(path[0] == 0);
            assert forall |s: int| 0 <= s < path.len() implies 0 <= #[trigger] path[s] <= 4000 by {
                assert(s == 0);
            }
            assert forall |s: int| 0 <= s < path.len() - 1 implies exists |i: int|
                0 <= i < reward_values.len()
                    && #[trigger] path[s] < #[trigger] reward_values[i] as int
                    && path[s + 1] == path[s] + reward_values[i] as int
            by {
                assert(false);
            }
        }
        assert(exists |p: Seq<int>| #[trigger] Self::reward_path_ok(reward_values, p)
            && p[p.len() - 1] == 0);
    }

    pub proof fn lemma_path_push_ok(reward_values: Seq<i32>, path: Seq<int>, total: int, i: int)
        requires
            Self::reward_path_ok(reward_values, path),
            path[path.len() - 1] == total,
            0 <= i < reward_values.len(),
            0 <= total < reward_values[i] as int,
            total + reward_values[i] as int <= 4000,
        ensures
            Self::reward_path_ok(reward_values, path.push(total + reward_values[i] as int)),
            path.push(total + reward_values[i] as int)[path.push(total + reward_values[i] as int).len() - 1]
                == total + reward_values[i] as int,
    {
        let next = total + reward_values[i] as int;
        let next_path = path.push(next);
        assert(next_path.len() == path.len() + 1);
        assert(next_path[0] == 0);
        assert(next_path[next_path.len() - 1] == next);
        assert forall |s: int| 0 <= s < next_path.len() implies 0 <= #[trigger] next_path[s] <= 4000 by {
            if s < path.len() {
                assert(next_path[s] == path[s]);
            } else {
                assert(s == path.len());
                assert(next_path[s] == next);
            }
        }
        assert forall |s: int| 0 <= s < next_path.len() - 1 implies exists |j: int|
            0 <= j < reward_values.len()
                && #[trigger] next_path[s] < #[trigger] reward_values[j] as int
                && next_path[s + 1] == next_path[s] + reward_values[j] as int
        by {
            if s < path.len() - 1 {
                assert(next_path[s] == path[s]);
                assert(next_path[s + 1] == path[s + 1]);
                assert(exists |j: int|
                    0 <= j < reward_values.len()
                        && #[trigger] path[s] < #[trigger] reward_values[j] as int
                        && path[s + 1] == path[s] + reward_values[j] as int);
            } else {
                assert(s == path.len() - 1);
                assert(next_path[s] == total);
                assert(next_path[s + 1] == next);
                assert(exists |j: int|
                    0 <= j < reward_values.len()
                        && #[trigger] next_path[s] < #[trigger] reward_values[j] as int
                        && next_path[s + 1] == next_path[s] + reward_values[j] as int) by {
                    assert(i == i);
                }
            }
        }
    }

    pub proof fn lemma_reachable_step(reward_values: Seq<i32>, total: int, i: int)
        requires
            Self::reward_reachable(reward_values, total),
            0 <= i < reward_values.len(),
            0 <= total < reward_values[i] as int,
            total + reward_values[i] as int <= 4000,
        ensures
            Self::reward_reachable(reward_values, total + reward_values[i] as int),
    {
        let path = choose |p: Seq<int>| #[trigger] Self::reward_path_ok(reward_values, p)
            && p[p.len() - 1] == total;
        Self::lemma_path_push_ok(reward_values, path, total, i);
        assert(exists |p: Seq<int>| #[trigger] Self::reward_path_ok(reward_values, p)
            && p[p.len() - 1] == total + reward_values[i] as int);
    }

    pub proof fn lemma_path_prefix_ok(reward_values: Seq<i32>, path: Seq<int>, end: int)
        requires
            Self::reward_path_ok(reward_values, path),
            1 <= end <= path.len(),
        ensures
            Self::reward_path_ok(reward_values, path.subrange(0, end)),
            path.subrange(0, end).len() == end,
            path.subrange(0, end)[end - 1] == path[end - 1],
    {
        let prefix = path.subrange(0, end);
        assert(prefix.len() == end);
        assert(prefix[0] == path[0]);
        assert forall |s: int| 0 <= s < prefix.len() implies 0 <= #[trigger] prefix[s] <= 4000 by {
            assert(prefix[s] == path[s]);
        }
        assert forall |s: int| 0 <= s < prefix.len() - 1 implies exists |i: int|
                0 <= i < reward_values.len()
                    && #[trigger] prefix[s] < #[trigger] reward_values[i] as int
                    && prefix[s + 1] == prefix[s] + reward_values[i] as int
        by {
            assert(prefix[s] == path[s]);
            assert(prefix[s + 1] == path[s + 1]);
            assert(exists |i: int|
                0 <= i < reward_values.len()
                    && #[trigger] path[s] < #[trigger] reward_values[i] as int
                    && path[s + 1] == path[s] + reward_values[i] as int);
        }
    }

    pub proof fn lemma_reachable_decompose(reward_values: Seq<i32>, total: int)
        requires
            Self::reward_reachable(reward_values, total),
            total > 0,
        ensures
            exists |i: int, previous: int|
                0 <= i < reward_values.len()
                    && 0 <= previous < #[trigger] reward_values[i] as int
                    && total == previous + reward_values[i] as int
                    && #[trigger] Self::reward_reachable(reward_values, previous),
    {
        let path = choose |p: Seq<int>| #[trigger] Self::reward_path_ok(reward_values, p)
            && p[p.len() - 1] == total;
        assert(path.len() > 1) by {
            if path.len() <= 1 {
                assert(path.len() == 1);
                assert(path[path.len() - 1] == path[0]);
                assert(total == 0);
                assert(false);
            }
        }
        let last = path.len() - 1;
        let step = path.len() - 2;
        let previous = path[step];
        assert(0 <= step < path.len() - 1);
        assert(exists |i: int|
            0 <= i < reward_values.len()
                && path[step] < #[trigger] reward_values[i] as int
                && path[step + 1] == path[step] + reward_values[i] as int);
        let i = choose |i: int|
            0 <= i < reward_values.len()
                && path[step] < #[trigger] reward_values[i] as int
                && path[step + 1] == path[step] + reward_values[i] as int;
        assert(step + 1 == last);
        assert(path[last] == total);
        assert(total == previous + reward_values[i] as int);
        Self::lemma_path_prefix_ok(reward_values, path, last);
        let prefix = path.subrange(0, last);
        assert(prefix[prefix.len() - 1] == previous);
        assert(Self::reward_reachable(reward_values, previous)) by {
            assert(exists |p: Seq<int>| #[trigger] Self::reward_path_ok(reward_values, p)
                && p[p.len() - 1] == previous);
        }
        assert(exists |j: int, prev: int|
            0 <= j < reward_values.len()
                && 0 <= prev < #[trigger] reward_values[j] as int
                && total == prev + reward_values[j] as int
                && #[trigger] Self::reward_reachable(reward_values, prev));
    }

    pub proof fn lemma_reachable_bound(reward_values: Seq<i32>, total: int)
        requires
            Self::reward_reachable(reward_values, total),
        ensures
            0 <= total <= 4000,
    {
        let path = choose |p: Seq<int>| #[trigger] Self::reward_path_ok(reward_values, p)
            && p[p.len() - 1] == total;
        assert(0 <= path.len() - 1 < path.len());
    }

    pub proof fn lemma_single_reachable(reward_values: Seq<i32>, total: int)
        requires
            reward_values.len() == 1,
            0 <= total,
            forall |i: int| 0 <= i < reward_values.len() ==> 1 <= #[trigger] reward_values[i] <= 2000,
            Self::reward_reachable(reward_values, total),
        ensures
            total == 0 || total == reward_values[0] as int,
        decreases total,
    {
        if total == 0 {
        } else {
            Self::lemma_reachable_decompose(reward_values, total);
            let (i, previous) = choose |i: int, previous: int|
                0 <= i < reward_values.len()
                    && 0 <= previous < #[trigger] reward_values[i] as int
                    && total == previous + reward_values[i] as int
                    && #[trigger] Self::reward_reachable(reward_values, previous);
            assert(i == 0);
            assert(previous < total) by (nonlinear_arith)
                requires
                    1 <= reward_values[i],
                    total == previous + reward_values[i] as int;
            Self::lemma_single_reachable(reward_values, previous);
            assert(previous == 0) by {
                if previous != 0 {
                    assert(previous == reward_values[0] as int);
                    assert(false) by (nonlinear_arith)
                        requires
                            previous == reward_values[0] as int,
                            previous < reward_values[0] as int;
                }
            }
        }
    }

    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn dp_reach(vals: Seq<i32>, i: int, s: int) -> bool
        decreases i,
    {
        if i <= 0 {
            s == 0
        } else {
            Self::dp_reach(vals, i - 1, s)
                || ((vals[i - 1] as int) <= s && s - (vals[i - 1] as int) < (vals[i - 1] as int)
                    && Self::dp_reach(vals, i - 1, s - vals[i - 1] as int))
        }
    }

    proof fn lemma_dp_reach_zero(vals: Seq<i32>, i: int)
        requires
            0 <= i,
        ensures
            Self::dp_reach(vals, i, 0),
        decreases i,
    {
        if i > 0 {
            Self::lemma_dp_reach_zero(vals, i - 1);
        }
    }

    proof fn lemma_dp_reach_mono(vals: Seq<i32>, i: int, i2: int, s: int)
        requires
            0 <= i <= i2 <= vals.len(),
            Self::dp_reach(vals, i, s),
        ensures
            Self::dp_reach(vals, i2, s),
        decreases i2 - i,
    {
        if i < i2 {
            Self::lemma_dp_reach_mono(vals, i, i2 - 1, s);
        }
    }

    proof fn lemma_dp_reach_not_4000(vals: Seq<i32>, i: int)
        requires
            0 <= i <= vals.len(),
            forall|p: int| 0 <= p < vals.len() ==> 1 <= #[trigger] vals[p] <= 2000,
        ensures
            !Self::dp_reach(vals, i, 4000),
        decreases i,
    {
        if i > 0 {
            Self::lemma_dp_reach_not_4000(vals, i - 1);
        }
    }

    proof fn lemma_dp_reach_to_reachable(reward_values: Seq<i32>, vals: Seq<i32>, i: int, s: int)
        requires
            vals.to_multiset() =~= reward_values.to_multiset(),
            0 <= i <= vals.len(),
            0 <= s <= 4000,
            Self::dp_reach(vals, i, s),
        ensures
            Self::reward_reachable(reward_values, s),
        decreases i,
    {
        if i <= 0 {
            Self::lemma_reachable_zero(reward_values);
        } else if Self::dp_reach(vals, i - 1, s) {
            Self::lemma_dp_reach_to_reachable(reward_values, vals, i - 1, s);
        } else {
            let v = vals[i - 1];
            let prev = s - v as int;
            assert(0 <= prev < s);
            Self::lemma_dp_reach_to_reachable(reward_values, vals, i - 1, prev);
            assert(vals.to_multiset().count(v) > 0) by {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
                assert(vals.contains(v));
            }
            assert(reward_values.to_multiset().count(v) > 0);
            assert(reward_values.contains(v)) by {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
            }
            let idx = choose|idx: int| 0 <= idx < reward_values.len() && reward_values[idx] == v;
            Self::lemma_reachable_step(reward_values, prev, idx);
            assert(prev + reward_values[idx] as int == s);
        }
    }

    proof fn lemma_reachable_to_dp_reach(reward_values: Seq<i32>, sorted_vals: Seq<i32>, total: int) -> (idx: int)
        requires
            sorted_vals.to_multiset() =~= reward_values.to_multiset(),
            Self::sorted(sorted_vals),
            Self::reward_reachable(reward_values, total),
        ensures
            -1 <= idx < sorted_vals.len(),
            idx == -1 ==> total == 0,
            idx >= 0 ==> sorted_vals[idx] as int <= total,
            idx >= 0 ==> Self::dp_reach(sorted_vals, idx + 1, total),
        decreases total,
    {
        if total == 0 {
            -1
        } else {
            Self::lemma_reachable_decompose(reward_values, total);
            let (i, previous) = choose|i: int, previous: int|
                0 <= i < reward_values.len()
                    && 0 <= previous < #[trigger] reward_values[i] as int
                    && total == previous + reward_values[i] as int
                    && #[trigger] Self::reward_reachable(reward_values, previous);
            let idx_prev = Self::lemma_reachable_to_dp_reach(reward_values, sorted_vals, previous);
            let v = reward_values[i];
            assert(reward_values.to_multiset().count(v) > 0) by {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
                assert(reward_values.contains(v));
            }
            assert(sorted_vals.to_multiset().count(v) > 0);
            assert(sorted_vals.contains(v)) by {
                broadcast use vstd::seq_lib::group_to_multiset_ensures;
            }
            let j0 = choose|j0: int| 0 <= j0 < sorted_vals.len() && sorted_vals[j0] == v;
            if idx_prev == -1 {
                Self::lemma_dp_reach_zero(sorted_vals, j0);
                assert(sorted_vals[j0] as int <= total);
                assert((total - sorted_vals[j0] as int) < (sorted_vals[j0] as int));
                assert(Self::dp_reach(sorted_vals, j0 + 1, total));
                j0
            } else {
                assert(sorted_vals[idx_prev] as int <= previous);
                assert(previous < v as int);
                assert((sorted_vals[idx_prev] as int) < (v as int));
                assert(j0 > idx_prev) by {
                    if j0 <= idx_prev {
                        assert(sorted_vals[j0] <= sorted_vals[idx_prev]);
                        assert(false);
                    }
                }
                Self::lemma_dp_reach_mono(sorted_vals, idx_prev + 1, j0, previous);
                assert(Self::dp_reach(sorted_vals, j0, previous));
                assert(sorted_vals[j0] as int <= total);
                assert((total - sorted_vals[j0] as int) < (sorted_vals[j0] as int));
                assert(Self::dp_reach(sorted_vals, j0 + 1, total));
                j0
            }
        }
    }

    proof fn lemma_rotate_multiset(pre: Seq<i32>, post: Seq<i32>, lo: int, hi: int)
        requires
            pre.len() == post.len(),
            0 <= lo <= hi < pre.len(),
            forall|k: int| (0 <= k < lo || hi < k < pre.len()) ==> post[k] == pre[k],
            post[lo] == pre[hi],
            forall|k: int| lo < k <= hi ==> post[k] == pre[k - 1],
        ensures
            post.to_multiset() =~= pre.to_multiset(),
    {
        broadcast use vstd::seq_lib::group_to_multiset_ensures;
        let n = pre.len() as int;
        assert(pre =~= pre.subrange(0, lo) + pre.subrange(lo, hi + 1) + pre.subrange(hi + 1, n));
        assert(post =~= post.subrange(0, lo) + post.subrange(lo, hi + 1) + post.subrange(hi + 1, n));
        assert(post.subrange(0, lo) =~= pre.subrange(0, lo));
        assert(post.subrange(hi + 1, n) =~= pre.subrange(hi + 1, n));
        let mid_pre = pre.subrange(lo, hi + 1);
        let mid_post = post.subrange(lo, hi + 1);
        let inner = pre.subrange(lo, hi);
        assert(mid_pre =~= inner.push(pre[hi]));
        assert(mid_post =~= seq![pre[hi]] + inner);
        assert(inner.push(pre[hi]) =~= inner + seq![pre[hi]]);
        vstd::seq_lib::lemma_seq_union_to_multiset_commutative(inner, seq![pre[hi]]);
        assert(mid_pre.to_multiset() =~= mid_post.to_multiset());
        vstd::seq_lib::lemma_multiset_commutative(pre.subrange(0, lo), mid_pre);
        vstd::seq_lib::lemma_multiset_commutative(pre.subrange(0, lo) + mid_pre, pre.subrange(hi + 1, n));
        vstd::seq_lib::lemma_multiset_commutative(post.subrange(0, lo), mid_post);
        vstd::seq_lib::lemma_multiset_commutative(post.subrange(0, lo) + mid_post, post.subrange(hi + 1, n));
        assert(pre.to_multiset() =~= pre.subrange(0, lo).to_multiset().add(mid_pre.to_multiset()).add(
            pre.subrange(hi + 1, n).to_multiset(),
        ));
        assert(post.to_multiset() =~= post.subrange(0, lo).to_multiset().add(mid_post.to_multiset()).add(
            post.subrange(hi + 1, n).to_multiset(),
        ));
    }

    pub fn max_total_reward(reward_values: Vec<i32>) -> (result: i32)
        requires
            1 <= reward_values.len() <= 2000,
            forall |i: int| 0 <= i < reward_values.len() ==> 1 <= #[trigger] reward_values[i] <= 2000,
        ensures
            Self::max_total_reward_spec(reward_values@, result as int),
    {
        if reward_values.len() == 1 {
            proof {
                Self::lemma_reachable_zero(reward_values@);
                Self::lemma_reachable_step(reward_values@, 0, 0);
                assert(Self::reward_reachable(reward_values@, reward_values[0] as int));
                assert forall |candidate: int| Self::reward_reachable(reward_values@, candidate)
                    implies candidate <= reward_values[0] as int
                by {
                    Self::lemma_reachable_bound(reward_values@, candidate);
                    Self::lemma_single_reachable(reward_values@, candidate);
                }
            }
            return reward_values[0];
        }
        let mut vals = reward_values.clone();
        let mut a = 1usize;
        while a < vals.len()
            invariant
                vals.len() == reward_values.len(),
                1 <= vals.len() <= 2000,
                1 <= a <= vals.len(),
                forall |p: int| 0 <= p < vals.len() ==> 1 <= #[trigger] vals[p] <= 2000,
                Self::sorted(vals@.subrange(0, a as int)),
                vals@.to_multiset() =~= reward_values@.to_multiset(),
            decreases vals.len() - a,
        {
            let key = vals[a];
            let ghost pre = vals@;
            let mut b = a;
            while b > 0 && vals[b - 1] > key
                invariant
                    vals.len() == reward_values.len(),
                    1 <= vals.len() <= 2000,
                    0 <= b <= a,
                    a < vals.len(),
                    1 <= key <= 2000,
                    forall |p: int| 0 <= p < vals.len() ==> 1 <= #[trigger] vals[p] <= 2000,
                    key == pre[a as int],
                    Self::sorted(pre.subrange(0, a as int)),
                    forall|k: int| 0 <= k <= b as int ==> vals@[k] == pre[k],
                    forall|k: int| b < k <= a ==> vals@[k] == pre[k - 1],
                    forall|k: int| a < k < vals.len() as int ==> vals@[k] == pre[k],
                    forall|m: int| b as int <= m < a as int ==> pre[m] as int > key as int,
                decreases b,
            {
                vals[b] = vals[b - 1];
                b -= 1;
            }
            assert(b > 0 ==> pre[b as int - 1] as int <= key as int);
            vals[b] = key;
            proof {
                Self::lemma_rotate_multiset(pre, vals@, b as int, a as int);
                let bi = b as int;
                let ai = a as int;
                assert(Self::sorted(vals@.subrange(0, ai + 1))) by {
                    assert forall|i: int, j: int| 0 <= i <= j < ai + 1
                        implies vals@[i] <= vals@[j]
                    by {
                        if i < bi && j < bi {
                            assert(vals@[i] == pre[i]);
                            assert(vals@[j] == pre[j]);
                            assert(pre.subrange(0, ai)[i] <= pre.subrange(0, ai)[j]);
                        } else if i < bi && j == bi {
                            assert(vals@[i] == pre[i]);
                            assert(vals@[j] == key);
                            assert(pre.subrange(0, ai)[i] <= pre.subrange(0, ai)[bi - 1]);
                        } else if i < bi && j > bi {
                            assert(vals@[i] == pre[i]);
                            assert(vals@[j] == pre[j - 1]);
                            assert(pre.subrange(0, ai)[i] <= pre.subrange(0, ai)[bi - 1]);
                            assert(pre[bi - 1] as int <= key as int);
                            assert(pre[j - 1] as int > key as int);
                        } else if i == bi && j == bi {
                        } else if i == bi && j > bi {
                            assert(vals@[i] == key);
                            assert(vals@[j] == pre[j - 1]);
                            assert(pre[j - 1] as int > key as int);
                        } else {
                            assert(i > bi && j > bi);
                            assert(vals@[i] == pre[i - 1]);
                            assert(vals@[j] == pre[j - 1]);
                            assert(pre.subrange(0, ai)[i - 1] <= pre.subrange(0, ai)[j - 1]);
                        }
                    }
                }
            }
            a += 1;
        }
        assert(vals@.subrange(0, a as int) =~= vals@);
        assert(Self::sorted(vals@));

        let mut reachable: Vec<bool> = vec![false; 4001];
        reachable[0] = true;
        proof {
            assert forall|t: int| 0 <= t <= 4000 implies reachable@[t] == Self::dp_reach(vals@, 0, t) by {
                if t == 0 {
                } else {
                    assert(!Self::dp_reach(vals@, 0, t));
                }
            }
        }

        let mut i = 0usize;
        while i < vals.len()
            invariant
                vals.len() == reward_values.len(),
                1 <= vals.len() <= 2000,
                reachable.len() == 4001,
                forall |p: int| 0 <= p < vals.len() ==> 1 <= #[trigger] vals[p] <= 2000,
                0 <= i <= vals.len(),
                forall|t: int| 0 <= t <= 4000 ==> reachable@[t] == Self::dp_reach(vals@, i as int, t),
                reachable@[4000] == false,
            decreases vals.len() - i,
        {
            let r = vals[i] as usize;
            let ghost old_r: Seq<bool> = reachable@;
            let mut s = 4000usize;
            let ghost mut boundary: int = 4000;
            loop
                invariant_except_break
                    reachable.len() == 4001,
                    0 <= s <= 4000,
                    boundary == s as int,
                    1 <= r <= 2000,
                    r == vals@[i as int] as usize,
                    forall|t: int| 0 <= t <= 4000 ==> old_r[t] == Self::dp_reach(vals@, i as int, t),
                    forall|t: int| 0 <= t <= 4000 ==>
                        #[trigger] reachable@[t] == (old_r[t]
                            || exists|src: int| #![trigger old_r[src]] boundary < src <= 4000 && old_r[src]
                                && src < r as int && t == src + r as int),
                ensures
                    reachable.len() == 4001,
                    boundary == -1,
                    1 <= r <= 2000,
                    r == vals@[i as int] as usize,
                    forall|t: int| 0 <= t <= 4000 ==> old_r[t] == Self::dp_reach(vals@, i as int, t),
                    forall|t: int| 0 <= t <= 4000 ==>
                        #[trigger] reachable@[t] == (old_r[t]
                            || exists|src: int| #![trigger old_r[src]] boundary < src <= 4000 && old_r[src]
                                && src < r as int && t == src + r as int),
                decreases s,
            {
                proof {
                    assert(reachable@[s as int] == old_r[s as int]) by {
                        if exists|src: int| boundary < src <= 4000 && old_r[src] && src < r as int
                            && (s as int) == src + r as int {
                            let src = choose|src: int| boundary < src <= 4000 && old_r[src] && src < r as int
                                && (s as int) == src + r as int;
                            assert(false);
                        }
                    }
                }
                if reachable[s] && s < r {
                    let t = s + r;
                    if t <= 4000 {
                        let ghost before_set = reachable@;
                        reachable[t] = true;
                        proof {
                            assert(old_r[s as int]);
                            assert forall|tt: int| 0 <= tt <= 4000 implies
                                reachable@[tt] == (old_r[tt]
                                    || exists|src: int| #![trigger old_r[src]] (s as int - 1) < src <= 4000 && old_r[src]
                                        && src < r as int && tt == src + r as int)
                            by {
                                if tt == t as int {
                                    assert(reachable@[tt]);
                                    assert((s as int - 1) < (s as int) <= 4000 && old_r[s as int]
                                        && (s as int) < r as int && tt == (s as int) + r as int);
                                } else {
                                    assert(reachable@[tt] == before_set[tt]);
                                    assert(before_set[tt] == (old_r[tt]
                                        || exists|src: int| boundary < src <= 4000 && old_r[src] && src < r as int
                                            && tt == src + r as int));
                                    if !old_r[tt] {
                                        if exists|src: int| boundary < src <= 4000 && old_r[src] && src < r as int
                                            && tt == src + r as int {
                                            let src = choose|src: int| boundary < src <= 4000 && old_r[src]
                                                && src < r as int && tt == src + r as int;
                                            assert((s as int - 1) < src <= 4000 && old_r[src] && src < r as int
                                                && tt == src + r as int);
                                        }
                                        if exists|src: int| (s as int - 1) < src <= 4000 && old_r[src]
                                            && src < r as int && tt == src + r as int {
                                            let src = choose|src: int| (s as int - 1) < src <= 4000 && old_r[src]
                                                && src < r as int && tt == src + r as int;
                                            if src == s as int {
                                                assert(tt == t as int);
                                                assert(false);
                                            } else {
                                                assert(boundary < src <= 4000 && old_r[src] && src < r as int
                                                    && tt == src + r as int);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        proof {
                            assert((s as int) + (r as int) > 4000);
                            assert forall|tt: int| 0 <= tt <= 4000 implies
                                reachable@[tt] == (old_r[tt]
                                    || exists|src: int| #![trigger old_r[src]] (s as int - 1) < src <= 4000 && old_r[src]
                                        && src < r as int && tt == src + r as int)
                            by {
                                assert(reachable@[tt] == (old_r[tt]
                                    || exists|src: int| boundary < src <= 4000 && old_r[src] && src < r as int
                                        && tt == src + r as int));
                                if !old_r[tt] {
                                    if exists|src: int| boundary < src <= 4000 && old_r[src] && src < r as int
                                        && tt == src + r as int {
                                        let src = choose|src: int| boundary < src <= 4000 && old_r[src]
                                            && src < r as int && tt == src + r as int;
                                        assert((s as int - 1) < src <= 4000 && old_r[src] && src < r as int
                                            && tt == src + r as int);
                                    }
                                    if exists|src: int| (s as int - 1) < src <= 4000 && old_r[src] && src < r as int
                                        && tt == src + r as int {
                                        let src = choose|src: int| (s as int - 1) < src <= 4000 && old_r[src]
                                            && src < r as int && tt == src + r as int;
                                        if src == s as int {
                                            assert(tt == (s as int) + (r as int));
                                            assert(false);
                                        } else {
                                            assert(boundary < src <= 4000 && old_r[src] && src < r as int
                                                && tt == src + r as int);
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    proof {
                        assert(!(old_r[s as int] && (s as int) < (r as int)));
                        assert forall|tt: int| 0 <= tt <= 4000 implies
                            reachable@[tt] == (old_r[tt]
                                || exists|src: int| #![trigger old_r[src]] (s as int - 1) < src <= 4000 && old_r[src]
                                    && src < r as int && tt == src + r as int)
                        by {
                            assert(reachable@[tt] == (old_r[tt]
                                || exists|src: int| boundary < src <= 4000 && old_r[src] && src < r as int
                                    && tt == src + r as int));
                            if !old_r[tt] {
                                if exists|src: int| boundary < src <= 4000 && old_r[src] && src < r as int
                                    && tt == src + r as int {
                                    let src = choose|src: int| boundary < src <= 4000 && old_r[src]
                                        && src < r as int && tt == src + r as int;
                                    assert((s as int - 1) < src <= 4000 && old_r[src] && src < r as int
                                        && tt == src + r as int);
                                }
                                if exists|src: int| (s as int - 1) < src <= 4000 && old_r[src] && src < r as int
                                    && tt == src + r as int {
                                    let src = choose|src: int| (s as int - 1) < src <= 4000 && old_r[src]
                                        && src < r as int && tt == src + r as int;
                                    if src == s as int {
                                        assert(false);
                                    } else {
                                        assert(boundary < src <= 4000 && old_r[src] && src < r as int
                                            && tt == src + r as int);
                                    }
                                }
                            }
                        }
                    }
                }
                proof {
                    boundary = s as int - 1;
                }
                if s == 0 {
                    break;
                }
                s -= 1;
            }
            proof {
                assert forall|t: int| 0 <= t <= 4000 implies reachable@[t] == Self::dp_reach(vals@, i as int + 1, t) by {
                    assert(old_r[t] == Self::dp_reach(vals@, i as int, t));
                    if reachable@[t] {
                        if old_r[t] {
                        } else {
                            let src = choose|src: int| -1 < src <= 4000 && old_r[src] && src < r as int
                                && t == src + r as int;
                            assert(old_r[src] == Self::dp_reach(vals@, i as int, src));
                            assert(Self::dp_reach(vals@, i as int, src));
                            assert((vals@[i as int] as int) <= t);
                            assert(t - (vals@[i as int] as int) < (vals@[i as int] as int));
                            assert(Self::dp_reach(vals@, i as int, t - vals@[i as int] as int));
                        }
                    } else {
                        if Self::dp_reach(vals@, i as int + 1, t) {
                            if Self::dp_reach(vals@, i as int, t) {
                                assert(old_r[t]);
                                assert(reachable@[t] == (old_r[t]
                                    || exists|src2: int| -1 < src2 <= 4000 && old_r[src2] && src2 < r as int
                                        && t == src2 + r as int));
                                assert(reachable@[t]);
                                assert(false);
                            } else {
                                let src = t - vals@[i as int] as int;
                                assert(old_r[src] == Self::dp_reach(vals@, i as int, src));
                                assert(old_r[src]);
                                assert(-1 < src <= 4000);
                                assert(src < r as int);
                                assert(t == src + r as int);
                                assert(reachable@[t] == (old_r[t]
                                    || exists|src2: int| -1 < src2 <= 4000 && old_r[src2] && src2 < r as int
                                        && t == src2 + r as int));
                                assert(reachable@[t]);
                                assert(false);
                            }
                        }
                    }
                }
            }
            i += 1;
        }

        proof {
            assert forall|t: int| 0 <= t <= 4000 implies reachable@[t] == Self::dp_reach(vals@, vals.len() as int, t) by {
            }
            Self::lemma_dp_reach_zero(vals@, vals.len() as int);
        }

        let mut ans = 0usize;
        let mut x = 0usize;
        while x <= 4000
            invariant_except_break
                reachable.len() == 4001,
                0 <= x <= 4000,
                forall|t: int| 0 <= t <= 4000 ==> reachable@[t] == Self::dp_reach(vals@, vals.len() as int, t),
                0 <= ans <= 4000,
                reachable@[ans as int],
                forall|t: int| 0 <= t < x as int ==> #[trigger] reachable@[t] ==> t <= ans as int,
            ensures
                reachable.len() == 4001,
                forall|t: int| 0 <= t <= 4000 ==> reachable@[t] == Self::dp_reach(vals@, vals.len() as int, t),
                0 <= ans <= 4000,
                reachable@[ans as int],
                forall|t: int| 0 <= t <= 4000 ==> #[trigger] reachable@[t] ==> t <= ans as int,
            decreases 4000 - x,
        {
            if reachable[x] {
                ans = x;
            }
            if x == 4000 {
                break;
            }
            x += 1;
        }

        proof {
            assert(Self::dp_reach(vals@, vals.len() as int, ans as int));
            Self::lemma_dp_reach_to_reachable(reward_values@, vals@, vals.len() as int, ans as int);
            assert(Self::reward_reachable(reward_values@, ans as int));
            assert forall|candidate: int| Self::reward_reachable(reward_values@, candidate)
                implies candidate <= ans as int
            by {
                let idx = Self::lemma_reachable_to_dp_reach(reward_values@, vals@, candidate);
                if idx == -1 {
                    assert(candidate == 0);
                } else {
                    assert(Self::dp_reach(vals@, idx + 1, candidate));
                    Self::lemma_reachable_bound(reward_values@, candidate);
                    Self::lemma_dp_reach_mono(vals@, idx + 1, vals.len() as int, candidate);
                    assert(Self::dp_reach(vals@, vals.len() as int, candidate));
                    assert(reachable@[candidate] == Self::dp_reach(vals@, vals.len() as int, candidate));
                    assert(reachable@[candidate]);
                }
            }
        }

        ans as i32
    }
}

}
