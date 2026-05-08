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
        while i < n {
            xs.push(points[i][0]);
            i = i + 1;
        }

        if n > 0 {
            let mut i2: usize = 1;
            while i2 < n {
                let mut j = i2;
                while j != 0 {
                    if xs[j - 1] > xs[j] {
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
        while p < n {
            let cover = xs[p] + w;
            p = p + 1;
            while p < n && xs[p] <= cover {
                p = p + 1;
            }
            ans = ans + 1;
        }

        ans
    }
}

}
