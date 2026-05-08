use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted_between(a: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub open spec fn x_prefix(points: Seq<Vec<i32>>, end: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            Seq::<i32>::empty()
        } else if end > points.len() {
            Self::x_prefix(points, points.len() as int)
        } else {
            Self::x_prefix(points, end - 1).push(points[end - 1][0])
        }
    }

    pub open spec fn x_seq(points: Seq<Vec<i32>>) -> Seq<i32> {
        Self::x_prefix(points, points.len() as int)
    }

    pub open spec fn min_rectangles_continue(s: Seq<i32>, w: int, start: int, cover: int) -> int
        decreases s.len() - start,
    {
        if start < 0 {
            Self::min_rectangles_continue(s, w, 0, cover)
        } else if start >= s.len() {
            0
        } else if s[start] as int <= cover {
            Self::min_rectangles_continue(s, w, start + 1, cover)
        } else {
            1 + Self::min_rectangles_continue(s, w, start + 1, s[start] as int + w)
        }
    }

    pub open spec fn min_rectangles_sorted_from(s: Seq<i32>, w: int, start: int) -> int
        decreases s.len() - start,
    {
        if start < 0 {
            Self::min_rectangles_sorted_from(s, w, 0)
        } else if start >= s.len() {
            0
        } else {
            1 + Self::min_rectangles_continue(s, w, start + 1, s[start] as int + w)
        }
    }

    proof fn lemma_continue_skip_prefix(s: Seq<i32>, w: int, start: int, cover: int, end: int)
        requires
            0 <= start <= end <= s.len(),
            forall|k: int| start <= k < end ==> s[k] as int <= cover,
        ensures
            Self::min_rectangles_continue(s, w, start, cover) == Self::min_rectangles_continue(s, w, end, cover),
        decreases end - start,
    {
        if start < end {
            assert(start < s.len());
            assert(s[start] as int <= cover);
            Self::lemma_continue_skip_prefix(s, w, start + 1, cover, end);
            assert(Self::min_rectangles_continue(s, w, start, cover) == Self::min_rectangles_continue(s, w, start + 1, cover));
        } else {
        }
    }

    proof fn lemma_continue_at_gt_equals_sorted(s: Seq<i32>, w: int, start: int, cover: int)
        requires
            0 <= start < s.len(),
            s[start] as int > cover,
        ensures
            Self::min_rectangles_continue(s, w, start, cover) == Self::min_rectangles_sorted_from(s, w, start),
    {
    }

    pub fn min_rectangles_to_cover_points(points: Vec<Vec<i32>>, w: i32) -> (result: i32)
        requires
            1 <= points.len() <= 100000,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][0] <= 1000000000,
            forall |i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][1] <= 1000000000,
            0 <= w <= 1000000000,
        ensures
            exists|s: Seq<i32>, r: Seq<int>|
                Self::sorted_between(s, 0, s.len() as int)
                && Self::is_reorder_of(r, s, Self::x_seq(points@))
                && result as int == Self::min_rectangles_sorted_from(s, w as int, 0),
    {
        let n = points.len();
        let mut xs: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100000,
                n == points.len(),
                0 <= i <= n,
                forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t].len() == 2,
                forall |t: int| 0 <= t < points.len() ==> 0 <= #[trigger] points[t][0] <= 1000000000,
                forall |t: int| 0 <= t < points.len() ==> 0 <= #[trigger] points[t][1] <= 1000000000,
                0 <= w <= 1000000000,
                xs.len() == i,
                xs@ == Self::x_prefix(points@, i as int),
                forall |t: int| 0 <= t < xs.len() ==> 0 <= #[trigger] xs[t] <= 1000000000,
            decreases n - i,
        {
            proof {
                assert(points[i as int].len() == 2);
            }
            let ghost old_xs_seq = xs@;
            xs.push(points[i][0]);
            proof {
                assert(xs@ == old_xs_seq.push(points[i as int][0]));
                assert(old_xs_seq == Self::x_prefix(points@, i as int));
                assert(Self::x_prefix(points@, i as int + 1)
                    == Self::x_prefix(points@, i as int).push(points[i as int][0]));
                assert(xs@ == Self::x_prefix(points@, i as int + 1));
            }
            i = i + 1;
        }

        proof {
            assert(i == n);
            assert(xs@ == Self::x_prefix(points@, n as int));
            assert(n as int == points@.len());
            assert(Self::x_seq(points@) == Self::x_prefix(points@, n as int));
            assert(xs@ == Self::x_seq(points@));
        }

        let ghost old_xs = xs@;
        proof {
            let r = Seq::new(xs@.len(), |k: int| k);
            assert(Self::is_reorder_of(r, xs@, old_xs));
            assert(old_xs == Self::x_seq(points@));
        }

        if n > 0 {
            let mut i2: usize = 1;
            while i2 < n
                invariant
                    1 <= n <= 100000,
                    n == xs.len(),
                    old_xs.len() == n as int,
                    1 <= i2 <= n,
                    0 <= w <= 1000000000,
                    forall |t: int| 0 <= t < xs.len() ==> 0 <= #[trigger] xs[t] <= 1000000000,
                    Self::sorted_between(xs@, 0, i2 as int),
                    exists|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs),
                decreases n - i2,
            {
                let mut j = i2;
                while j != 0
                    invariant
                        1 <= n <= 100000,
                        n == xs.len(),
                        old_xs.len() == n as int,
                        0 <= j <= i2 < n,
                        0 <= w <= 1000000000,
                        forall |t: int| 0 <= t < xs.len() ==> 0 <= #[trigger] xs[t] <= 1000000000,
                        forall|x: int, y: int| 0 <= x <= y <= i2 as int ==> x != j as int && y != j as int ==> xs[x] <= xs[y],
                        Self::sorted_between(xs@, j as int, i2 as int + 1),
                        exists|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs),
                    decreases j,
                {
                    if xs[j - 1] > xs[j] {
                        proof {
                            let r1 = choose|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs);
                            let r2 = r1.update(j - 1, r1[j as int]).update(j as int, r1[j - 1]);
                            assert(Self::is_reorder_of(
                                r2,
                                xs@.update(j - 1, xs@[j as int]).update(j as int, xs@[j - 1]),
                                old_xs,
                            ));
                        }
                        let left = xs[j - 1];
                        let right = xs[j];
                        xs.set(j - 1, right);
                        xs.set(j, left);
                    }
                    j = j - 1;
                }
                i2 = i2 + 1;
            }
        }

        let mut ans: i32 = 0;
        let mut p: usize = 0;
        while p < n
            invariant
                1 <= n <= 100000,
                n == xs.len(),
                old_xs.len() == n as int,
                0 <= w <= 1000000000,
                0 <= p <= n,
                0 <= ans as int <= p as int,
                forall |t: int| 0 <= t < xs.len() ==> 0 <= #[trigger] xs[t] <= 1000000000,
                Self::sorted_between(xs@, 0, n as int),
                exists|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs),
                ans as int + Self::min_rectangles_sorted_from(xs@, w as int, p as int)
                    == Self::min_rectangles_sorted_from(xs@, w as int, 0),
            decreases n - p,
        {
            let ghost old_p = p as int;
            let ghost old_ans = ans as int;
            proof {
                assert(old_p < n as int);
                assert(0 <= xs[old_p] as int <= 1000000000);
                assert(0 <= w as int <= 1000000000);
                assert(xs[old_p] as int + w as int <= 2000000000);
            }
            let cover = xs[p] + w;
            p = p + 1;
            while p < n && xs[p] <= cover
                invariant
                    1 <= n <= 100000,
                    n == xs.len(),
                    old_xs.len() == n as int,
                    0 <= w <= 1000000000,
                    old_p < n as int,
                    old_ans + Self::min_rectangles_sorted_from(xs@, w as int, old_p)
                        == Self::min_rectangles_sorted_from(xs@, w as int, 0),
                    old_ans <= old_p,
                    old_p + 1 <= p as int <= n as int,
                    cover as int == xs[old_p] as int + w as int,
                    forall |t: int| old_p + 1 <= t < p as int ==> xs[t] as int <= cover as int,
                    forall |t: int| 0 <= t < xs.len() ==> 0 <= #[trigger] xs[t] <= 1000000000,
                    Self::sorted_between(xs@, 0, n as int),
                    exists|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs),
                decreases n - p,
            {
                p = p + 1;
            }

            proof {
                if p < n {
                    assert(!(xs[p as int] <= cover));
                    assert(xs[p as int] as int > cover as int);
                }
                Self::lemma_continue_skip_prefix(xs@, w as int, old_p + 1, cover as int, p as int);
                assert(Self::min_rectangles_continue(xs@, w as int, old_p + 1, cover as int)
                    == Self::min_rectangles_continue(xs@, w as int, p as int, cover as int));
                if p < n {
                    Self::lemma_continue_at_gt_equals_sorted(xs@, w as int, p as int, cover as int);
                    assert(Self::min_rectangles_continue(xs@, w as int, p as int, cover as int)
                        == Self::min_rectangles_sorted_from(xs@, w as int, p as int));
                } else {
                    assert(p as int == n as int);
                    assert(Self::min_rectangles_continue(xs@, w as int, p as int, cover as int) == 0);
                    assert(Self::min_rectangles_sorted_from(xs@, w as int, p as int) == 0);
                }
                assert(Self::min_rectangles_sorted_from(xs@, w as int, old_p)
                    == 1 + Self::min_rectangles_sorted_from(xs@, w as int, p as int));
            }

            ans = ans + 1;
            proof {
                assert(ans as int == old_ans + 1);
                assert(ans as int + Self::min_rectangles_sorted_from(xs@, w as int, p as int)
                    == Self::min_rectangles_sorted_from(xs@, w as int, 0));
                assert(old_ans <= old_p);
                assert(old_p + 1 <= p as int);
                assert(ans as int <= p as int);
            }
        }

        proof {
            assert(p == n);
            assert(Self::min_rectangles_sorted_from(xs@, w as int, n as int) == 0);
            assert(ans as int == Self::min_rectangles_sorted_from(xs@, w as int, 0));
            assert(old_xs == Self::x_seq(points@));

            let r_final = choose|r: Seq<int>| Self::is_reorder_of(r, xs@, old_xs);
            assert(exists|s: Seq<i32>, r: Seq<int>|
                Self::sorted_between(s, 0, s.len() as int)
                && Self::is_reorder_of(r, s, Self::x_seq(points@))
                && ans as int == Self::min_rectangles_sorted_from(s, w as int, 0)) by {
                let s = xs@;
                let r = r_final;
                assert(Self::sorted_between(s, 0, s.len() as int));
                assert(Self::is_reorder_of(r, s, Self::x_seq(points@)));
                assert(ans as int == Self::min_rectangles_sorted_from(s, w as int, 0));
            };
        }

        ans
    }
}

}
