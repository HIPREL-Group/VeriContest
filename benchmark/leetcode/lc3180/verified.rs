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
            decreases vals.len() - a,
        {
            let key = vals[a];
            let mut b = a;
            while b > 0 && vals[b - 1] > key
                invariant
                    vals.len() == reward_values.len(),
                    1 <= vals.len() <= 2000,
                    0 <= b <= a,
                    a < vals.len(),
                    1 <= key <= 2000,
                    forall |p: int| 0 <= p < vals.len() ==> 1 <= #[trigger] vals[p] <= 2000,
                decreases b,
            {
                vals.set(b, vals[b - 1]);
                b -= 1;
            }
            vals.set(b, key);
            a += 1;
        }

        let mut reachable: Vec<bool> = vec![false; 4001];
        reachable[0] = true;

        let mut i = 0usize;
        while i < vals.len()
            invariant
                vals.len() == reward_values.len(),
                1 <= vals.len() <= 2000,
                reachable.len() == 4001,
                reachable[4000] == false,
                forall |p: int| 0 <= p < vals.len() ==> 1 <= #[trigger] vals[p] <= 2000,
                0 <= i <= vals.len(),
            decreases vals.len() - i,
        {
            let r = vals[i] as usize;
            let mut s = 4000usize;
            loop
                invariant
                    reachable.len() == 4001,
                    reachable[4000] == false,
                    0 <= s <= 4000,
                    1 <= r <= 2000,
                decreases s,
            {
                if reachable[s] && s < r {
                    let t = s + r;
                    if t <= 4000 {
                        reachable[t] = true;
                    }
                }
                if s == 0 {
                    break;
                }
                s -= 1;
            }
            i += 1;
        }

        let mut ans = 0usize;
        let mut x = 0usize;
        while x <= 4000
            invariant
                reachable.len() == 4001,
                0 <= x <= 4000,
                reachable[4000] == false,
                0 <= ans < 4000,
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

        let mut reach2: Vec<bool> = vec![false; 4001];
        reach2.set(0, true);
        proof {
            Self::lemma_reachable_zero(reward_values@);
        }
        assert(reach2[0]);
        assert forall |t: int| 0 <= t < 4001 && #[trigger] reach2[t]
            implies Self::reward_reachable(reward_values@, t)
        by {
            assert(t == 0);
        }
        let mut s2 = 0usize;
        while s2 <= 4000
            invariant
                1 <= reward_values.len() <= 2000,
                forall |i: int| 0 <= i < reward_values.len() ==> 1 <= #[trigger] reward_values[i] <= 2000,
                reach2.len() == 4001,
                reach2[0],
                0 <= s2 <= 4001,
                forall |t: int| 0 <= t < 4001 && #[trigger] reach2[t]
                    ==> Self::reward_reachable(reward_values@, t),
                forall |t: int| 0 <= t < s2 && Self::reward_reachable(reward_values@, t)
                    ==> #[trigger] reach2[t],
                forall |p: int, j: int|
                    0 <= p < s2 && 0 <= j < reward_values.len()
                        && #[trigger] reach2[p]
                        && p < reward_values[j] as int
                        && p + reward_values[j] as int <= 4000
                    ==> #[trigger] reach2[p + reward_values[j] as int],
            decreases 4001 - s2,
        {
            if reach2[s2] {
                let mut j2 = 0usize;
                while j2 < reward_values.len()
                    invariant
                        1 <= reward_values.len() <= 2000,
                        forall |i: int| 0 <= i < reward_values.len() ==> 1 <= #[trigger] reward_values[i] <= 2000,
                        reach2.len() == 4001,
                        reach2[0],
                        0 <= s2 <= 4000,
                        0 <= j2 <= reward_values.len(),
                        reach2[s2 as int],
                        forall |t: int| 0 <= t < 4001 && #[trigger] reach2[t]
                            ==> Self::reward_reachable(reward_values@, t),
                        forall |t: int| 0 <= t < s2 && Self::reward_reachable(reward_values@, t)
                            ==> #[trigger] reach2[t],
                        forall |p: int, j: int|
                            0 <= p < s2 && 0 <= j < reward_values.len()
                                && #[trigger] reach2[p]
                                && p < reward_values[j] as int
                                && p + reward_values[j] as int <= 4000
                            ==> #[trigger] reach2[p + reward_values[j] as int],
                        forall |j: int|
                            0 <= j < j2
                                && (s2 as int) < reward_values[j] as int
                                && (s2 as int) + reward_values[j] as int <= 4000
                            ==> #[trigger] reach2[(s2 as int) + reward_values[j] as int],
                    decreases reward_values.len() - j2,
                {
                    let r = reward_values[j2] as usize;
                    if s2 < r {
                        let target = s2 + r;
                        if target <= 4000 {
                            proof {
                                assert(Self::reward_reachable(reward_values@, s2 as int));
                                assert(0 <= j2 < reward_values@.len());
                                assert(s2 as int + reward_values@[j2 as int] as int == target as int);
                                Self::lemma_reachable_step(reward_values@, s2 as int, j2 as int);
                                assert(Self::reward_reachable(reward_values@, target as int));
                            }
                            reach2.set(target, true);
                        }
                    }
                    j2 += 1;
                }
            }
            assert(Self::reward_reachable(reward_values@, s2 as int) ==> reach2[s2 as int]) by {
                if Self::reward_reachable(reward_values@, s2 as int) {
                    if s2 == 0 {
                        assert(reach2[0]);
                    } else {
                        Self::lemma_reachable_decompose(reward_values@, s2 as int);
                        assert(exists |j: int, previous: int|
                            0 <= j < reward_values@.len()
                                && 0 <= previous < #[trigger] reward_values@[j] as int
                                && s2 as int == previous + reward_values@[j] as int
                                && #[trigger] Self::reward_reachable(reward_values@, previous));
                        let (j, previous) = choose |j: int, previous: int|
                            0 <= j < reward_values@.len()
                                && 0 <= previous < #[trigger] reward_values@[j] as int
                                && s2 as int == previous + reward_values@[j] as int
                                && #[trigger] Self::reward_reachable(reward_values@, previous);
                        assert(previous < s2 as int) by (nonlinear_arith)
                            requires
                                1 <= reward_values@[j],
                                s2 as int == previous + reward_values@[j] as int;
                        assert(0 <= previous < s2 as int);
                        assert(reach2[previous]);
                        assert(previous + reward_values@[j] as int <= 4000);
                        assert(reach2[previous + reward_values@[j] as int]);
                        assert(reach2[s2 as int]);
                    }
                }
            }
            assert forall |t: int| 0 <= t < s2 + 1 && Self::reward_reachable(reward_values@, t)
                implies #[trigger] reach2[t]
            by {
                if t < s2 {
                } else {
                    assert(t == s2);
                }
            }
            if s2 < 4000 {
                s2 += 1;
            } else {
                s2 = 4001;
            }
        }

        ans = 0usize;
        assert(reach2[0]);
        let mut y = 0usize;
        while y <= 4000
            invariant
                reach2.len() == 4001,
                reach2[0],
                0 <= y <= 4001,
                0 <= ans <= 4000,
                reach2[ans as int],
                forall |t: int| 0 <= t < 4001 && #[trigger] reach2[t]
                    ==> Self::reward_reachable(reward_values@, t),
                forall |t: int| 0 <= t < 4001 && Self::reward_reachable(reward_values@, t)
                    ==> #[trigger] reach2[t],
                forall |t: int| 0 <= t < y && #[trigger] reach2[t] ==> t <= ans,
            decreases 4001 - y,
        {
            if reach2[y] {
                ans = y;
            }
            if y < 4000 {
                y += 1;
            } else {
                y = 4001;
            }
        }
        proof {
            assert(Self::reward_reachable(reward_values@, ans as int));
            assert forall |candidate: int| Self::reward_reachable(reward_values@, candidate)
                implies candidate <= ans as int
            by {
                Self::lemma_reachable_bound(reward_values@, candidate);
                assert(0 <= candidate < 4001);
                assert(reach2[candidate]);
            }
        }
        ans as i32
    }
}

}
