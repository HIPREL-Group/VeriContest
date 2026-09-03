use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_overlaps_window(start: int, d: int, l: int, r: int) -> bool {
        start <= r && l <= start + d - 1
    }

    pub open spec fn spec_overlap_count_prefix(start: int, d: int, left: Seq<i32>, right: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto <= left.len(),
            left.len() == right.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::spec_overlap_count_prefix(start, d, left, right, upto - 1)
                + if Self::spec_overlaps_window(start, d, left[upto - 1] as int, right[upto - 1] as int) {
                    1int
                } else {
                    0int
                }
        }
    }

    pub open spec fn spec_overlap_count(start: int, d: int, left: Seq<i32>, right: Seq<i32>) -> int
        recommends
            left.len() == right.len(),
    {
        Self::spec_overlap_count_prefix(start, d, left, right, left.len() as int)
    }

    pub open spec fn spec_diff_prefix_sum(diff: Seq<i32>, start: int) -> int
        decreases start,
    {
        if start <= 0 {
            0
        } else {
            Self::spec_diff_prefix_sum(diff, start - 1) + diff[start] as int
        }
    }

    proof fn lemma_diff_prefix_sum_all_zero(diff: Seq<i32>, start: int)
        requires
            0 <= start < diff.len(),
            forall|k: int| 0 <= k < diff.len() ==> diff[k] == 0,
        ensures
            Self::spec_diff_prefix_sum(diff, start) == 0,
        decreases start,
    {
        if start > 0 {
            Self::lemma_diff_prefix_sum_all_zero(diff, start - 1);
        }
    }

    proof fn lemma_diff_prefix_sum_point_update(old_diff: Seq<i32>, new_diff: Seq<i32>, li: int, hi1: int, start: int)
        requires
            1 <= li < hi1 < old_diff.len(),
            new_diff.len() == old_diff.len(),
            0 <= start < old_diff.len(),
            forall|p: int| #![trigger new_diff[p]] 0 <= p < old_diff.len() && p != li && p != hi1 ==> new_diff[p] == old_diff[p],
            new_diff[li] == old_diff[li] + 1,
            new_diff[hi1] == old_diff[hi1] - 1,
        ensures
            Self::spec_diff_prefix_sum(new_diff, start) ==
                Self::spec_diff_prefix_sum(old_diff, start)
                    + (if li <= start < hi1 { 1int } else { 0int }),
        decreases start,
    {
        if start > 0 {
            Self::lemma_diff_prefix_sum_point_update(old_diff, new_diff, li, hi1, start - 1);
            if start == li {
                assert(new_diff[start] == old_diff[start] + 1);
            } else if start == hi1 {
                assert(new_diff[start] == old_diff[start] - 1);
            } else {
                assert(new_diff[start] == old_diff[start]);
            }
        }
    }

    proof fn lemma_overlap_count_prefix_bounds(start: int, d: int, left: Seq<i32>, right: Seq<i32>, upto: int)
        requires
            0 <= upto <= left.len(),
            left.len() == right.len(),
        ensures
            0 <= Self::spec_overlap_count_prefix(start, d, left, right, upto) <= upto,
        decreases upto,
    {
        if upto > 0 {
            Self::lemma_overlap_count_prefix_bounds(start, d, left, right, upto - 1);
        }
    }

    pub fn overlaps_window(start: i32, d: i32, l: i32, r: i32) -> (res: bool)
        requires
            1 <= d,
        ensures
            res == Self::spec_overlaps_window(start as int, d as int, l as int, r as int),
    {
        (start as i64) <= (r as i64) && (l as i64) <= (start as i64) + (d as i64) - 1
    }

    pub fn overlap_count(start: i32, d: i32, left: &Vec<i32>, right: &Vec<i32>) -> (res: i32)
        requires
            1 <= d,
            left.len() == right.len(),
            left.len() <= i32::MAX,
            forall|j: int| 0 <= j < left.len() as int ==> 1 <= #[trigger] left[j] <= right[j],
        ensures
            res as int == Self::spec_overlap_count(start as int, d as int, left@, right@),
            0 <= res <= left.len() as i32,
    {
        let mut cnt: i32 = 0;
        let mut j: usize = 0;
        while j < left.len()
            invariant
                1 <= d,
                left.len() == right.len(),
                left.len() <= i32::MAX,
                forall|x: int| 0 <= x < left.len() as int ==> 1 <= #[trigger] left[x] <= right[x],
                0 <= j <= left.len(),
                0 <= cnt <= j as i32,
                cnt as int == Self::spec_overlap_count_prefix(start as int, d as int, left@, right@, j as int),
            decreases left.len() - j,
        {
            if Self::overlaps_window(start, d, left[j], right[j]) {
                cnt = cnt + 1;
            }
            proof {
                assert(Self::spec_overlap_count_prefix(start as int, d as int, left@, right@, j as int + 1)
                    == Self::spec_overlap_count_prefix(start as int, d as int, left@, right@, j as int)
                        + if Self::spec_overlaps_window(start as int, d as int, left[j as int] as int, right[j as int] as int) { 1int } else { 0int });
            }
            j = j + 1;
        }
        cnt
    }

    pub fn best_start_days(n: i32, d: i32, left: Vec<i32>, right: Vec<i32>) -> (res: (i32, i32))
        requires
            1 <= n,
            n <= 100000,
            1 <= d <= n,
            1 <= left.len() <= n as nat,
            left.len() == right.len(),
            forall|j: int| 0 <= j < left.len() as int ==> 1 <= #[trigger] left[j] <= right[j] <= n,
        ensures
            1 <= res.0 <= n - d + 1,
            1 <= res.1 <= n - d + 1,
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    ==> Self::spec_overlap_count(res.0 as int, d as int, left@, right@)
                        >= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@),
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    ==> Self::spec_overlap_count(res.1 as int, d as int, left@, right@)
                        <= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@),
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                        == Self::spec_overlap_count(res.0 as int, d as int, left@, right@)
                    ==> res.0 as int <= s,
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                        == Self::spec_overlap_count(res.1 as int, d as int, left@, right@)
                    ==> res.1 as int <= s,
    {
        let m = n - d + 1;
        let mm = m as usize;
        assert(1 <= m <= 100000);
        assert(mm <= 100000);

        let mut diff: Vec<i32> = Vec::with_capacity(mm + 2);
        let mut p: usize = 0;
        while p < mm + 2
            invariant
                mm <= 100000,
                p <= mm + 2,
                diff.len() == p,
                forall|k: int| 0 <= k < p as int ==> diff[k] == 0,
            decreases mm + 2 - p,
        {
            diff.push(0);
            p += 1;
        }

        proof {
            assert forall|start: int| 1 <= start <= mm as int implies
                Self::spec_diff_prefix_sum(diff@, start) == 0
            by {
                Self::lemma_diff_prefix_sum_all_zero(diff@, start);
            }
        }

        let mut j: usize = 0;
        while j < left.len()
            invariant
                1 <= d <= n,
                n <= 100000,
                m == n - d + 1,
                mm == m as usize,
                1 <= mm,
                left.len() == right.len(),
                1 <= left.len() <= n as nat,
                forall|k: int| 0 <= k < left.len() as int ==> 1 <= #[trigger] left[k] <= right[k] <= n,
                diff.len() == mm + 2,
                0 <= j <= left.len(),
                forall|k: int| 0 <= k < diff.len() as int ==> -(j as int) <= #[trigger] diff[k] <= j as int,
                forall|start: int| 1 <= start <= mm as int ==>
                    Self::spec_diff_prefix_sum(diff@, start)
                        == Self::spec_overlap_count_prefix(start, d as int, left@, right@, j as int),
            decreases left.len() - j,
        {
            let l = left[j];
            let r = right[j];
            let lo = if l - d + 1 > 1 { l - d + 1 } else { 1 };
            let hi = if r < m { r } else { m };
            if lo <= hi {
                let li = lo as usize;
                let hi1 = (hi + 1) as usize;
                let ghost old_diff = diff@;
                diff[li] = diff[li] + 1;
                diff[hi1] = diff[hi1] - 1;
                proof {
                    assert forall|start: int| 1 <= start <= mm as int implies
                        Self::spec_diff_prefix_sum(diff@, start)
                            == Self::spec_overlap_count_prefix(start, d as int, left@, right@, j as int + 1)
                    by {
                        Self::lemma_diff_prefix_sum_point_update(old_diff, diff@, li as int, hi1 as int, start);
                    }
                }
            } 
            j += 1;
        }

        proof {
            assert forall|start: int| 1 <= start <= mm as int implies
                0 <= #[trigger] Self::spec_overlap_count(start, d as int, left@, right@) <= left.len() as int
            by {
                Self::lemma_overlap_count_prefix_bounds(start, d as int, left@, right@, left.len() as int);
            }
        }
        assert(diff.len() == mm + 2);
        assert(forall|k: int| 0 <= k < diff.len() as int ==> -(left.len() as int) <= #[trigger] diff[k] <= left.len() as int);

        let mut best_bro: i32 = 1;
        let mut best_mom: i32 = 1;
        let mut best_bro_count: i32 = i32::MIN;
        let mut best_mom_count: i32 = i32::MAX;

        let mut cur: i32 = 0;
        let mut start: usize = 1;
        while start <= mm
            invariant
                mm == m as usize,
                1 <= mm <= 100000,
                1 <= left.len() <= 100000,
                diff.len() == mm + 2,
                1 <= start <= mm + 1,
                forall|s: int| 1 <= s <= mm as int ==>
                    Self::spec_diff_prefix_sum(diff@, s) == Self::spec_overlap_count(s, d as int, left@, right@),
                forall|s: int| 1 <= s <= mm as int ==>
                    0 <= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@) <= left.len() as int,
                forall|k: int| 0 <= k < diff.len() as int ==> -(left.len() as int) <= #[trigger] diff[k] <= left.len() as int,
                cur as int == Self::spec_diff_prefix_sum(diff@, start as int - 1),
                (start == 1 && best_bro_count == i32::MIN && best_mom_count == i32::MAX && best_bro == 1 && best_mom == 1)
                ||
                (start > 1
                    && 1 <= best_bro < start
                    && 1 <= best_mom < start
                    && best_bro_count as int == Self::spec_overlap_count(best_bro as int, d as int, left@, right@)
                    && best_mom_count as int == Self::spec_overlap_count(best_mom as int, d as int, left@, right@)
                    && (forall|s: int| 1 <= s < start as int ==>
                        Self::spec_overlap_count(best_bro as int, d as int, left@, right@)
                            >= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@))
                    && (forall|s: int| 1 <= s < start as int ==>
                        Self::spec_overlap_count(best_mom as int, d as int, left@, right@)
                            <= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@))
                    && (forall|s: int| 1 <= s < start as int
                        && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                            == Self::spec_overlap_count(best_bro as int, d as int, left@, right@)
                        ==> best_bro as int <= s)
                    && (forall|s: int| 1 <= s < start as int
                        && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                            == Self::spec_overlap_count(best_mom as int, d as int, left@, right@)
                        ==> best_mom as int <= s)
                ),
            decreases mm + 1 - start,
        {
            proof {
                if start > 1 {
                    assert(0 <= Self::spec_overlap_count(start as int - 1, d as int, left@, right@) <= left.len() as int);
                    assert(Self::spec_diff_prefix_sum(diff@, start as int - 1)
                        == Self::spec_overlap_count(start as int - 1, d as int, left@, right@));
                }
                assert(0 <= Self::spec_overlap_count(start as int, d as int, left@, right@) <= left.len() as int);
                assert(Self::spec_diff_prefix_sum(diff@, start as int)
                    == Self::spec_overlap_count(start as int, d as int, left@, right@));
                assert(Self::spec_diff_prefix_sum(diff@, start as int)
                    == Self::spec_diff_prefix_sum(diff@, start as int - 1) + diff@[start as int] as int);
                assert(diff@[start as int] as int
                    == Self::spec_diff_prefix_sum(diff@, start as int) - Self::spec_diff_prefix_sum(diff@, start as int - 1));
                assert(-(left.len() as int) <= diff[start as int] <= left.len() as int);
            }
            cur += diff[start];

            proof {
                assert(cur as int == Self::spec_overlap_count(start as int, d as int, left@, right@));
            }

            let old_best_bro = best_bro;
            let old_best_mom = best_mom;
            let old_best_bro_count = best_bro_count;
            let old_best_mom_count = best_mom_count;

            if cur > best_bro_count {
                best_bro_count = cur;
                best_bro = start as i32;
            }
            if cur < best_mom_count {
                best_mom_count = cur;
                best_mom = start as i32;
            }

            proof {
                if start == 1 {
                    assert(best_bro_count as int == Self::spec_overlap_count(best_bro as int, d as int, left@, right@));
                    assert(best_mom_count as int == Self::spec_overlap_count(best_mom as int, d as int, left@, right@));
                    assert forall|s: int| 1 <= s < start as int + 1 implies
                        Self::spec_overlap_count(best_bro as int, d as int, left@, right@)
                            >= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                    by {
                        assert(s == start as int);
                    };
                    assert forall|s: int| 1 <= s < start as int + 1 implies
                        Self::spec_overlap_count(best_mom as int, d as int, left@, right@)
                            <= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                    by {
                        assert(s == start as int);
                    };
                    assert forall|s: int| 1 <= s < start as int + 1
                        && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                            == Self::spec_overlap_count(best_bro as int, d as int, left@, right@)
                        implies best_bro as int <= s
                    by {
                        assert(s == start as int);
                    };
                    assert forall|s: int| 1 <= s < start as int + 1
                        && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                            == Self::spec_overlap_count(best_mom as int, d as int, left@, right@)
                        implies best_mom as int <= s
                    by {
                        assert(s == start as int);
                    };
                } else {
                    if cur > old_best_bro_count {
                        assert(best_bro == start as i32);
                        assert(best_bro_count == cur);
                    } else {
                        assert(best_bro == old_best_bro);
                        assert(best_bro_count == old_best_bro_count);
                    }
                    if cur < old_best_mom_count {
                        assert(best_mom == start as i32);
                        assert(best_mom_count == cur);
                    } else {
                        assert(best_mom == old_best_mom);
                        assert(best_mom_count == old_best_mom_count);
                    }

                    assert forall|s: int| 1 <= s < start as int + 1 implies
                        Self::spec_overlap_count(best_bro as int, d as int, left@, right@)
                            >= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                    by {
                        if s < start as int {
                            assert(Self::spec_overlap_count(old_best_bro as int, d as int, left@, right@)
                                >= Self::spec_overlap_count(s, d as int, left@, right@));
                        } else {
                            assert(s == start as int);
                        }
                    };
                    assert forall|s: int| 1 <= s < start as int + 1 implies
                        Self::spec_overlap_count(best_mom as int, d as int, left@, right@)
                            <= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                    by {
                        if s < start as int {
                            assert(Self::spec_overlap_count(old_best_mom as int, d as int, left@, right@)
                                <= Self::spec_overlap_count(s, d as int, left@, right@));
                        } else {
                            assert(s == start as int);
                        }
                    };
                    assert forall|s: int| 1 <= s < start as int + 1
                        && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                            == Self::spec_overlap_count(best_bro as int, d as int, left@, right@)
                        implies best_bro as int <= s
                    by {
                        if s < start as int {
                            if cur > old_best_bro_count {
                                assert(Self::spec_overlap_count(s, d as int, left@, right@)
                                    <= Self::spec_overlap_count(old_best_bro as int, d as int, left@, right@));
                                assert(false);
                            } else {
                                assert(old_best_bro as int <= s);
                            }
                        }
                    };
                    assert forall|s: int| 1 <= s < start as int + 1
                        && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                            == Self::spec_overlap_count(best_mom as int, d as int, left@, right@)
                        implies best_mom as int <= s
                    by {
                        if s < start as int {
                            if cur < old_best_mom_count {
                                assert(Self::spec_overlap_count(s, d as int, left@, right@)
                                    >= Self::spec_overlap_count(old_best_mom as int, d as int, left@, right@));
                                assert(false);
                            } else {
                                assert(old_best_mom as int <= s);
                            }
                        }
                    };
                }
            }

            start += 1;
        }

        (best_bro, best_mom)
    }
}

}
