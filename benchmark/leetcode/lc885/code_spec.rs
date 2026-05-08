use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn result_coords(res: Seq<Vec<i32>>) -> Seq<(int, int)>
        recommends
            forall |i: int| 0 <= i < res.len() ==> #[trigger] res[i].len() == 2,
    {
        Seq::new(res.len(), |i: int| (res[i][0] as int, res[i][1] as int))
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn in_bounds(rows: int, cols: int, row: int, col: int) -> bool {
        0 <= row < rows && 0 <= col < cols
    }

    pub open spec fn max_layer(rows: int, cols: int, r_start: int, c_start: int) -> int
        recommends
            1 <= rows,
            1 <= cols,
            0 <= r_start < rows,
            0 <= c_start < cols,
    {
        Self::max2(
            Self::max2(r_start, rows - 1 - r_start),
            Self::max2(c_start, cols - 1 - c_start),
        )
    }

    pub open spec fn east_segment(r_start: int, c_start: int, k: int, len: int) -> Seq<(int, int)>
        recommends
            1 <= k,
            0 <= len <= 2 * k,
    {
        Seq::new(len as nat, |i: int| (r_start - k + 1 + i, c_start + k))
    }

    pub open spec fn south_segment(r_start: int, c_start: int, k: int, len: int) -> Seq<(int, int)>
        recommends
            1 <= k,
            0 <= len <= 2 * k,
    {
        Seq::new(len as nat, |i: int| (r_start + k, c_start + k - 1 - i))
    }

    pub open spec fn west_segment(r_start: int, c_start: int, k: int, len: int) -> Seq<(int, int)>
        recommends
            1 <= k,
            0 <= len <= 2 * k,
    {
        Seq::new(len as nat, |i: int| (r_start + k - 1 - i, c_start - k))
    }

    pub open spec fn north_segment(r_start: int, c_start: int, k: int, len: int) -> Seq<(int, int)>
        recommends
            1 <= k,
            0 <= len <= 2 * k,
    {
        Seq::new(len as nat, |i: int| (r_start - k, c_start - k + 1 + i))
    }

    pub open spec fn filter_in_bounds(points: Seq<(int, int)>, rows: int, cols: int) -> Seq<(int, int)>
        decreases points.len()
    {
        if points.len() == 0 {
            seq![]
        } else {
            let prefix = points.subrange(0, points.len() - 1);
            let last = points[points.len() - 1];
            if Self::in_bounds(rows, cols, last.0, last.1) {
                Self::filter_in_bounds(prefix, rows, cols).push(last)
            } else {
                Self::filter_in_bounds(prefix, rows, cols)
            }
        }
    }

    pub open spec fn ring_coords(rows: int, cols: int, r_start: int, c_start: int, k: int) -> Seq<(int, int)>
        recommends
            1 <= k,
    {
        Self::filter_in_bounds(Self::east_segment(r_start, c_start, k, 2 * k), rows, cols)
        + Self::filter_in_bounds(Self::south_segment(r_start, c_start, k, 2 * k), rows, cols)
        + Self::filter_in_bounds(Self::west_segment(r_start, c_start, k, 2 * k), rows, cols)
        + Self::filter_in_bounds(Self::north_segment(r_start, c_start, k, 2 * k), rows, cols)
    }

    pub open spec fn spiral_coords(rows: int, cols: int, r_start: int, c_start: int, layers: nat) -> Seq<(int, int)>
        recommends
            1 <= rows,
            1 <= cols,
            0 <= r_start < rows,
            0 <= c_start < cols,
        decreases layers,
    {
        if layers == 0 {
            seq![(r_start, c_start)]
        } else {
            Self::spiral_coords(rows, cols, r_start, c_start, (layers - 1) as nat)
            + Self::ring_coords(rows, cols, r_start, c_start, layers as int)
        }
    }

    fn max2_exec(a: i32, b: i32) -> (m: i32)
        ensures
            m as int == Self::max2(a as int, b as int),
    {
        if a >= b { a } else { b }
    }

    pub fn spiral_matrix_iii(rows: i32, cols: i32, r_start: i32, c_start: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= rows <= 100,
            1 <= cols <= 100,
            0 <= r_start < rows,
            0 <= c_start < cols,
        ensures
            Self::result_coords(res@) == Self::spiral_coords(rows as int, cols as int, r_start as int, c_start as int, Self::max_layer(rows as int, cols as int, r_start as int, c_start as int) as nat),
    {
        let limit = Self::max2_exec(
            Self::max2_exec(r_start, rows - 1 - r_start),
            Self::max2_exec(c_start, cols - 1 - c_start),
        );

        let mut res: Vec<Vec<i32>> = Vec::new();
        let first = vec![r_start, c_start];
        res.push(first);

        let mut k: i32 = 1;
        while k <= limit {
            let side_len = 2 * k;

            let mut i: i32 = 0;
            while i < side_len {
                let r = r_start as i64 - k as i64 + 1 + i as i64;
                let c = c_start as i64 + k as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let pair = vec![rr, cc];
                    res.push(pair);
                }
                i += 1;
            }

            i = 0;
            while i < side_len {
                let r = r_start as i64 + k as i64;
                let c = c_start as i64 + k as i64 - 1 - i as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let pair = vec![rr, cc];
                    res.push(pair);
                }
                i += 1;
            }

            i = 0;
            while i < side_len {
                let r = r_start as i64 + k as i64 - 1 - i as i64;
                let c = c_start as i64 - k as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let pair = vec![rr, cc];
                    res.push(pair);
                }
                i += 1;
            }

            i = 0;
            while i < side_len {
                let r = r_start as i64 - k as i64;
                let c = c_start as i64 - k as i64 + 1 + i as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let pair = vec![rr, cc];
                    res.push(pair);
                }
                i += 1;
            }

            k += 1;
        }

        res
    }
}

}
