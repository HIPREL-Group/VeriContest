use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tap_left(ranges: Seq<i32>, t: int) -> int {
        t - ranges[t] as int
    }

    pub open spec fn tap_right(ranges: Seq<i32>, t: int) -> int {
        t + ranges[t] as int
    }

    pub open spec fn is_valid_covering(ranges: Seq<i32>, n: int, sel: Seq<int>) -> bool {
        sel.len() >= 1
        && (forall |k: int| 0 <= k < sel.len() ==> 0 <= #[trigger] sel[k] < ranges.len())
        && Self::tap_left(ranges, sel[0]) <= 0
        && Self::tap_right(ranges, sel[sel.len() - 1 as int]) >= n
        && (forall |k: int|
            #![trigger sel[k]]
            #![trigger sel[k + 1]]
            0 <= k < sel.len() - 1 ==>
            Self::tap_right(ranges, sel[k]) >= Self::tap_left(ranges, sel[k + 1]))
    }

    pub open spec fn spec_clamped_left(t: int, r: int) -> int {
        if t - r < 0 { 0 } else { t - r }
    }

    proof fn lemma_chain_induction(
        ranges: Seq<i32>, n: int, sel: Seq<int>, stuck_pos: int, m: int,
    )
        requires
            n >= 1,
            ranges.len() == n + 1,
            forall |i: int| 0 <= i < ranges.len() ==> 0 <= #[trigger] ranges[i] <= 100,
            sel.len() >= 1,
            forall |k: int| 0 <= k < sel.len() ==> 0 <= #[trigger] sel[k] < ranges.len(),
            Self::tap_left(ranges, sel[0]) <= 0,
            forall |k: int|
                #![trigger sel[k]]
                #![trigger sel[k + 1]]
                0 <= k < sel.len() - 1 ==>
                Self::tap_right(ranges, sel[k]) >= Self::tap_left(ranges, sel[k + 1]),
            0 <= stuck_pos < n,
            forall |t: int| 0 <= t < ranges.len() && Self::tap_left(ranges, t) <= stuck_pos
                ==> Self::tap_right(ranges, t) <= stuck_pos,
            0 <= m < sel.len(),
        ensures
            Self::tap_left(ranges, sel[m]) <= stuck_pos,
            Self::tap_right(ranges, sel[m]) <= stuck_pos,
        decreases m
    {
        if m == 0 {
            assert(Self::tap_left(ranges, sel[0]) <= 0 <= stuck_pos);
        } else {
            Self::lemma_chain_induction(ranges, n, sel, stuck_pos, m - 1);
        }
    }

    proof fn lemma_no_covering_when_stuck(
        ranges: Seq<i32>, n: int, stuck_pos: int,
    )
        requires
            n >= 1,
            ranges.len() == n + 1,
            forall |i: int| 0 <= i < ranges.len() ==> 0 <= #[trigger] ranges[i] <= 100,
            0 <= stuck_pos < n,
            forall |t: int| 0 <= t < ranges.len() && Self::tap_left(ranges, t) <= stuck_pos
                ==> Self::tap_right(ranges, t) <= stuck_pos,
        ensures
            forall |sel: Seq<int>| !Self::is_valid_covering(ranges, n, sel),
    {
        assert forall |sel: Seq<int>| !Self::is_valid_covering(ranges, n, sel) by {
            if sel.len() >= 1
                && (forall |k: int| 0 <= k < sel.len() ==> 0 <= #[trigger] sel[k] < ranges.len())
                && Self::tap_left(ranges, sel[0]) <= 0
                && (forall |k: int|
                    #![trigger sel[k]]
                    #![trigger sel[k + 1]]
                    0 <= k < sel.len() - 1 ==>
                    Self::tap_right(ranges, sel[k]) >= Self::tap_left(ranges, sel[k + 1]))
            {
                let last = sel.len() - 1;
                Self::lemma_chain_induction(ranges, n, sel, stuck_pos, last as int);
                assert(Self::tap_right(ranges, sel[last as int]) <= stuck_pos);
                assert(stuck_pos < n);
            }
        }
    }

    proof fn lemma_greedy_stays_ahead(
        ranges: Seq<i32>, n: int, mr: Seq<i32>,
        sel: Seq<int>, greedy_ends: Seq<int>, m: int,
    )
        requires
            n >= 1,
            ranges.len() == n + 1,
            mr.len() == n + 1,
            forall |i: int| 0 <= i < ranges.len() ==> 0 <= #[trigger] ranges[i] <= 100,
            forall |t: int| 0 <= t <= n && ranges[t] > 0 ==>
                #[trigger] mr[Self::spec_clamped_left(t, ranges[t] as int)] >= t + ranges[t] as int,
            forall |j: int| 0 <= j <= n ==> #[trigger] mr[j] >= 0,
            Self::is_valid_covering(ranges, n, sel),
            greedy_ends.len() >= 2,
            greedy_ends[0] == 0,
            forall |k: int| 0 < k < greedy_ends.len() ==>
                0 < #[trigger] greedy_ends[k],
            forall |k: int| 0 < k < greedy_ends.len() ==>
                greedy_ends[k - 1] < #[trigger] greedy_ends[k],
            forall |k: int| 0 < k < greedy_ends.len() ==>
                forall |p: int| 0 <= p <= greedy_ends[k - 1]
                    ==> mr[p] <= #[trigger] greedy_ends[k],
            1 <= m < greedy_ends.len(),
            m <= sel.len(),
        ensures
            Self::tap_right(ranges, sel[m - 1]) <= greedy_ends[m],
        decreases m
    {
        if m == 1 {
            let t0 = sel[0];
            assert(Self::tap_left(ranges, t0) <= 0);
            assert(0 <= t0 < ranges.len());
            let left_c = Self::spec_clamped_left(t0, ranges[t0] as int);
            assert(left_c == 0) by {
                assert(Self::tap_left(ranges, t0) <= 0);
                assert(left_c == Self::spec_clamped_left(t0, ranges[t0] as int));
            }
            if ranges[t0] > 0 {
                assert(mr[left_c] >= t0 + ranges[t0] as int);
                assert(mr[0] >= Self::tap_right(ranges, t0));
                assert(0 <= 0 <= greedy_ends[0]);
                assert(mr[0] <= greedy_ends[1]);
            } else {
                assert(Self::tap_right(ranges, t0) == t0 as int);
                assert(t0 as int <= 0);
            }
        } else {
            Self::lemma_greedy_stays_ahead(ranges, n, mr, sel, greedy_ends, m - 1);
            let prev_right = Self::tap_right(ranges, sel[m - 2]);
            assert(prev_right <= greedy_ends[m - 1]);
            let t_m = sel[m - 1];
            assert(0 <= t_m < ranges.len());
            assert(Self::tap_left(ranges, t_m) <= prev_right);
            let left_c = Self::spec_clamped_left(t_m, ranges[t_m] as int);
            assert(left_c <= prev_right);
            assert(left_c <= greedy_ends[m - 1]);
            if ranges[t_m] > 0 {
                assert(mr[left_c] >= t_m + ranges[t_m] as int);
                assert(mr[left_c] >= Self::tap_right(ranges, t_m));
                assert(0 <= left_c <= greedy_ends[m - 1]);
                assert(mr[left_c] <= greedy_ends[m]);
            } else {
                assert(Self::tap_right(ranges, t_m) == t_m as int);
                assert(Self::tap_left(ranges, t_m) == t_m as int);
                assert(t_m as int <= greedy_ends[m - 1]);
                assert(greedy_ends[m - 1] < greedy_ends[m]);
            }
        }
    }

    pub fn min_taps(n: i32, ranges: Vec<i32>) -> (res: i32)
        requires
            1 <= n <= 10_000,
            ranges.len() == n + 1,
            forall |i: int| 0 <= i < ranges.len() ==> 0 <= #[trigger] ranges[i] <= 100,
        ensures
            res == -1 || res >= 1,
            res == -1 ==> forall |sel: Seq<int>|
                !Self::is_valid_covering(ranges@, n as int, sel),
            res >= 1 ==> exists |sel: Seq<int>|
                #[trigger] Self::is_valid_covering(ranges@, n as int, sel)
                && sel.len() == res as nat,
            res >= 1 ==> forall |sel: Seq<int>|
                Self::is_valid_covering(ranges@, n as int, sel)
                ==> sel.len() >= res as nat,
    {
        let mut max_reach: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n as usize
            invariant
                1 <= n <= 10_000,
                0 <= k <= n as usize + 1,
                max_reach.len() == k,
                forall |m: int| 0 <= m < k ==> #[trigger] max_reach[m] == 0i32,
            decreases (n as usize + 1) - k,
        {
            max_reach.push(0i32);
            k = k + 1;
        }

        let ghost mut mr_achiever: Seq<int> = Seq::new(max_reach@.len(), |_j: int| 0int);

        let mut i: usize = 0;
        while i <= n as usize
            invariant
                0 <= i <= n as usize + 1,
                max_reach.len() == n + 1,
                ranges.len() == n + 1,
                1 <= n <= 10_000,
                forall |idx: int| 0 <= idx < ranges.len() ==> 0 <= #[trigger] ranges[idx] <= 100,
                forall |j: int| 0 <= j <= n ==> #[trigger] max_reach[j] >= 0,
                forall |j: int| 0 <= j <= n ==> max_reach[j] <= n + 100,
                forall |t: int| 0 <= t < i && ranges[t] > 0 ==>
                    #[trigger] max_reach[Self::spec_clamped_left(t, ranges[t] as int)]
                    >= t + ranges[t] as int,
                mr_achiever.len() == (n + 1) as nat,
                forall |j_idx: int| 0 <= j_idx <= n as int && max_reach@[j_idx] > 0i32 ==> (
                    0 <= #[trigger] mr_achiever[j_idx] < i as int
                    && ranges@[mr_achiever[j_idx]] > 0
                    && Self::spec_clamped_left(mr_achiever[j_idx], ranges@[mr_achiever[j_idx]] as int) == j_idx
                    && mr_achiever[j_idx] + ranges@[mr_achiever[j_idx]] as int == max_reach@[j_idx] as int
                ),
            decreases (n as usize + 1) - i,
        {
            let r = ranges[i];
            if r > 0 {
                let left: usize = if (i as i32) >= r { i - r as usize } else { 0 };
                let right: i32 = i as i32 + r;
                if right > max_reach[left] {
                    proof {
                        assert(left as int == Self::spec_clamped_left(i as int, r as int));
                        let new_mr = max_reach@.update(left as int, right);
                        let new_ach = mr_achiever.update(left as int, i as int);
                        assert forall |t: int| 0 <= t < i && ranges[t] > 0 implies
                            #[trigger] new_mr
                            [Self::spec_clamped_left(t, ranges[t] as int)]
                            >= t + ranges[t] as int
                        by {
                            let cl = Self::spec_clamped_left(t, ranges[t] as int);
                            if cl == left as int {
                                assert(new_mr[cl] == right);
                                assert(max_reach[cl] >= t + ranges[t] as int);
                                assert(right >= max_reach[cl]);
                            } else {
                                assert(new_mr[cl] == max_reach[cl]);
                            }
                        }
                        assert forall |j_idx: int| 0 <= j_idx <= n as int && new_mr[j_idx] > 0i32
                            implies (
                                0 <= #[trigger] new_ach[j_idx] <= i as int
                                && ranges@[new_ach[j_idx]] > 0
                                && Self::spec_clamped_left(new_ach[j_idx], ranges@[new_ach[j_idx]] as int) == j_idx
                                && new_ach[j_idx] + ranges@[new_ach[j_idx]] as int == new_mr[j_idx] as int
                            )
                        by {
                            if j_idx == left as int {
                                assert(new_ach[j_idx] == i as int);
                                assert(new_mr[j_idx] == right);
                            } else {
                                assert(new_ach[j_idx] == mr_achiever[j_idx]);
                                assert(new_mr[j_idx] == max_reach@[j_idx]);
                            }
                        }
                        mr_achiever = new_ach;
                    }
                    max_reach.set(left, right);
                }
            }
            i = i + 1;
        }

        let ghost mr = max_reach@;
        let ghost mr_ach = mr_achiever;

        let mut end: i32 = 0;
        let mut far: i32 = 0;
        let mut cnt: i32 = 0;
        let ghost mut greedy_ends: Seq<int> = seq![0int];
        let ghost mut witness_taps: Seq<int> = Seq::empty();
        let ghost mut far_witness: int = 0;

        let mut j: usize = 0;
        while j <= n as usize
            invariant
                0 <= j <= n as usize + 1,
                max_reach.len() == n + 1,
                ranges.len() == n + 1,
                max_reach@ == mr,
                1 <= n <= 10_000,
                forall |idx: int| 0 <= idx < ranges.len() ==> 0 <= #[trigger] ranges[idx] <= 100,
                forall |jj: int| 0 <= jj <= n ==> #[trigger] max_reach[jj] >= 0,
                forall |jj: int| 0 <= jj <= n ==> max_reach[jj] <= n + 100,
                forall |t: int| 0 <= t <= n && ranges[t] > 0 ==>
                    #[trigger] mr[Self::spec_clamped_left(t, ranges[t] as int)]
                    >= t + ranges[t] as int,
                0 <= end <= 10100i32,
                0 <= far <= 10100i32,
                0 <= cnt <= 10000i32,
                end >= cnt,
                far >= end,
                j as i32 <= end || end >= n,
                forall |p: int| 0 <= p < j ==> #[trigger] mr[p] <= far,
                cnt == greedy_ends.len() - 1,
                greedy_ends.len() >= 1,
                greedy_ends[0] == 0,
                end == greedy_ends[greedy_ends.len() - 1 as int],
                forall |g: int| 0 < g < greedy_ends.len() ==>
                    greedy_ends[g - 1] < #[trigger] greedy_ends[g],
                forall |g: int| 0 < g < greedy_ends.len() ==>
                    0 < #[trigger] greedy_ends[g],
                forall |g: int| 0 < g < greedy_ends.len() ==>
                    forall |p: int| 0 <= p <= greedy_ends[g - 1]
                        ==> mr[p] <= #[trigger] greedy_ends[g],
                end >= n ==> cnt >= 1,
                mr_ach.len() == (n + 1) as nat,
                forall |j_idx: int| 0 <= j_idx <= n as int && mr[j_idx] > 0i32 ==> (
                    0 <= #[trigger] mr_ach[j_idx] <= n as int
                    && ranges@[mr_ach[j_idx]] > 0
                    && Self::spec_clamped_left(mr_ach[j_idx], ranges@[mr_ach[j_idx]] as int) == j_idx
                    && mr_ach[j_idx] + ranges@[mr_ach[j_idx]] as int == mr[j_idx] as int
                ),
                0 <= far_witness <= n as int,
                mr[far_witness] >= far,
                far == 0 ==> far_witness == 0,
                far > 0 ==> far_witness < j as int,
                witness_taps.len() == cnt as nat,
                forall |wk: int| 0 <= wk < witness_taps.len() ==> (
                    0 <= #[trigger] witness_taps[wk] < ranges@.len()
                    && ranges@[witness_taps[wk]] > 0
                    && Self::spec_clamped_left(witness_taps[wk], ranges@[witness_taps[wk]] as int)
                        <= greedy_ends[wk]
                    && Self::tap_right(ranges@, witness_taps[wk]) >= greedy_ends[wk + 1]
                ),
                forall |g: int| 0 <= g < greedy_ends.len() - 1 ==> greedy_ends[g] < n as int,
            decreases (n as usize + 1) - j,
        {
            if j as i32 > end {
                proof {
                    assert(end >= n);
                    assert(j as i32 > n);
                    assert(false);
                }
                return -1;
            }
            if max_reach[j] > far {
                proof { far_witness = j as int; }
                far = max_reach[j];
            }
            if j as i32 == end && end < n {
                if far <= end {
                    proof {
                        let stuck = end as int;
                        assert(j as int == end as int);
                        assert forall |p: int| 0 <= p <= stuck implies #[trigger] mr[p] <= far by {
                            if p < j as int {
                            } else {
                                assert(p == j as int);
                                assert(mr[p] == max_reach[j as int]);
                                assert(max_reach[j as int] <= far);
                            }
                        }
                        assert forall |t: int| 0 <= t < ranges.len()
                            && Self::tap_left(ranges@, t) <= stuck
                            implies Self::tap_right(ranges@, t) <= stuck
                        by {
                            let cl = Self::spec_clamped_left(t, ranges@[t] as int);
                            if ranges@[t] > 0 {
                                assert(cl <= stuck);
                                assert(0 <= cl <= n as int);
                                assert(mr[cl] >= t + ranges@[t] as int);
                                assert(mr[cl] <= far as int);
                                assert(far <= end);
                            } else {
                                assert(Self::tap_right(ranges@, t) == t as int);
                                assert(Self::tap_left(ranges@, t) == t as int);
                            }
                        }
                        Self::lemma_no_covering_when_stuck(ranges@, n as int, stuck);
                    }
                    return -1;
                }
                proof {
                    assert(far > end);
                    assert(far > 0);
                    assert(mr[far_witness] >= far as int);
                    assert(mr[far_witness] > 0i32);
                    let tap_idx = mr_ach[far_witness];
                    assert(0 <= tap_idx <= n as int);
                    assert(tap_idx < ranges@.len());
                    assert(ranges@[tap_idx] > 0);
                    assert(Self::spec_clamped_left(tap_idx, ranges@[tap_idx] as int) == far_witness);
                    assert(tap_idx + ranges@[tap_idx] as int == mr[far_witness] as int);
                    assert(Self::tap_right(ranges@, tap_idx) >= far as int);
                    assert(far_witness <= j as int);
                    assert(j as int == end as int);
                    assert(Self::spec_clamped_left(tap_idx, ranges@[tap_idx] as int) <= end as int);
                    assert(end as int == greedy_ends[greedy_ends.len() - 1 as int]);

                    witness_taps = witness_taps.push(tap_idx);
                    greedy_ends = greedy_ends.push(far as int);

                    assert(greedy_ends[greedy_ends.len() - 1 as int] == far as int);
                    assert(greedy_ends[greedy_ends.len() - 2] == end as int);
                    assert(far > end);
                }
                end = far;
                cnt = cnt + 1;
            }
            j = j + 1;
        }

        proof {
            if cnt == 0 {
                assert(end == 0);
                assert(j as int > n as int);
                assert(0 <= n as int);
                assert(n as int <= end as int + 1 - 1);
                assert(n as int <= 0);
                assert(n >= 1);
                assert(false);
            }

            assert(cnt >= 1);
            assert(end >= n);

            assert(witness_taps.len() >= 1) by { assert(witness_taps.len() == cnt as nat); }

            assert forall |k: int| 0 <= k < witness_taps.len() implies
                0 <= #[trigger] witness_taps[k] < ranges@.len()
            by {};

            let t0 = witness_taps[0];
            let cl0 = Self::spec_clamped_left(t0, ranges@[t0] as int);
            assert(cl0 <= greedy_ends[0]);
            assert(greedy_ends[0] == 0);
            assert(Self::tap_left(ranges@, t0) <= cl0) by {}
            assert(Self::tap_left(ranges@, t0) <= 0);

            let last_k = (cnt - 1) as int;
            assert(Self::tap_right(ranges@, witness_taps[last_k]) >= greedy_ends[last_k + 1]);
            assert(last_k + 1 == cnt as int);
            assert(greedy_ends[cnt as int] == end as int);
            assert(Self::tap_right(ranges@, witness_taps[last_k]) >= n as int);

            assert forall |k: int|
                #![trigger witness_taps[k]]
                #![trigger witness_taps[k + 1]]
                0 <= k < witness_taps.len() - 1 implies
                Self::tap_right(ranges@, witness_taps[k]) >= Self::tap_left(ranges@, witness_taps[k + 1])
            by {
                let tk = witness_taps[k];
                let tk1 = witness_taps[k + 1];
                assert(Self::tap_right(ranges@, tk) >= greedy_ends[k + 1]);
                let cl1 = Self::spec_clamped_left(tk1, ranges@[tk1] as int);
                assert(cl1 <= greedy_ends[k + 1]);
                assert(Self::tap_left(ranges@, tk1) <= cl1);
            };

            assert(Self::is_valid_covering(ranges@, n as int, witness_taps));

            assert forall |sel: Seq<int>| Self::is_valid_covering(ranges@, n as int, sel)
                implies sel.len() >= cnt as nat
            by {
                if sel.len() < cnt as nat {
                    let m = sel.len() as int;
                    assert(1 <= m);
                    assert(m < greedy_ends.len());
                    assert(m <= sel.len());
                    Self::lemma_greedy_stays_ahead(ranges@, n as int, mr, sel, greedy_ends, m);
                    assert(Self::tap_right(ranges@, sel[m - 1]) <= greedy_ends[m]);
                    assert(Self::tap_right(ranges@, sel[sel.len() - 1 as int]) >= n as int);
                    assert(greedy_ends[m] < n as int);
                    assert(false);
                }
            };
        }

        cnt
    }
}

}

