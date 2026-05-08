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

    proof fn lemma_result_coords_push(points: Seq<Vec<i32>>, pair: Vec<i32>)
        requires
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            pair.len() == 2,
        ensures
            Self::result_coords(points.push(pair)) == Self::result_coords(points).push((pair[0] as int, pair[1] as int)),
    {
        assert(Self::result_coords(points.push(pair)).len() == Self::result_coords(points).push((pair[0] as int, pair[1] as int)).len());
        assert forall |i: int|
            0 <= i < Self::result_coords(points.push(pair)).len()
            implies Self::result_coords(points.push(pair))[i] == Self::result_coords(points).push((pair[0] as int, pair[1] as int))[i]
        by {
            if i < points.len() {
            } else {
                assert(i == points.len());
            }
        }
    }

    proof fn lemma_filter_append(points: Seq<(int, int)>, rows: int, cols: int, point: (int, int))
        ensures
            Self::filter_in_bounds(points.push(point), rows, cols)
                == if Self::in_bounds(rows, cols, point.0, point.1) {
                    Self::filter_in_bounds(points, rows, cols).push(point)
                } else {
                    Self::filter_in_bounds(points, rows, cols)
                },
    {
        assert(points.push(point).subrange(0, points.len() as int) == points);
    }

    proof fn lemma_east_segment_extend(r_start: int, c_start: int, k: int, len: int)
        requires
            1 <= k,
            0 <= len < 2 * k,
        ensures
            Self::east_segment(r_start, c_start, k, len + 1)
                == Self::east_segment(r_start, c_start, k, len).push((r_start - k + 1 + len, c_start + k)),
    {
        assert(Self::east_segment(r_start, c_start, k, len + 1).len() == Self::east_segment(r_start, c_start, k, len).push((r_start - k + 1 + len, c_start + k)).len());
        assert forall |i: int|
            0 <= i < Self::east_segment(r_start, c_start, k, len + 1).len()
            implies #[trigger] Self::east_segment(r_start, c_start, k, len + 1)[i]
                == Self::east_segment(r_start, c_start, k, len).push((r_start - k + 1 + len, c_start + k))[i]
        by {
            if i < len {
            } else {
                assert(i == len);
            }
        }
    }

    proof fn lemma_south_segment_extend(r_start: int, c_start: int, k: int, len: int)
        requires
            1 <= k,
            0 <= len < 2 * k,
        ensures
            Self::south_segment(r_start, c_start, k, len + 1)
                == Self::south_segment(r_start, c_start, k, len).push((r_start + k, c_start + k - 1 - len)),
    {
        assert(Self::south_segment(r_start, c_start, k, len + 1).len() == Self::south_segment(r_start, c_start, k, len).push((r_start + k, c_start + k - 1 - len)).len());
        assert forall |i: int|
            0 <= i < Self::south_segment(r_start, c_start, k, len + 1).len()
            implies #[trigger] Self::south_segment(r_start, c_start, k, len + 1)[i]
                == Self::south_segment(r_start, c_start, k, len).push((r_start + k, c_start + k - 1 - len))[i]
        by {
            if i < len {
            } else {
                assert(i == len);
            }
        }
    }

    proof fn lemma_west_segment_extend(r_start: int, c_start: int, k: int, len: int)
        requires
            1 <= k,
            0 <= len < 2 * k,
        ensures
            Self::west_segment(r_start, c_start, k, len + 1)
                == Self::west_segment(r_start, c_start, k, len).push((r_start + k - 1 - len, c_start - k)),
    {
        assert(Self::west_segment(r_start, c_start, k, len + 1).len() == Self::west_segment(r_start, c_start, k, len).push((r_start + k - 1 - len, c_start - k)).len());
        assert forall |i: int|
            0 <= i < Self::west_segment(r_start, c_start, k, len + 1).len()
            implies #[trigger] Self::west_segment(r_start, c_start, k, len + 1)[i]
                == Self::west_segment(r_start, c_start, k, len).push((r_start + k - 1 - len, c_start - k))[i]
        by {
            if i < len {
            } else {
                assert(i == len);
            }
        }
    }

    proof fn lemma_north_segment_extend(r_start: int, c_start: int, k: int, len: int)
        requires
            1 <= k,
            0 <= len < 2 * k,
        ensures
            Self::north_segment(r_start, c_start, k, len + 1)
                == Self::north_segment(r_start, c_start, k, len).push((r_start - k, c_start - k + 1 + len)),
    {
        assert(Self::north_segment(r_start, c_start, k, len + 1).len() == Self::north_segment(r_start, c_start, k, len).push((r_start - k, c_start - k + 1 + len)).len());
        assert forall |i: int|
            0 <= i < Self::north_segment(r_start, c_start, k, len + 1).len()
            implies #[trigger] Self::north_segment(r_start, c_start, k, len + 1)[i]
                == Self::north_segment(r_start, c_start, k, len).push((r_start - k, c_start - k + 1 + len))[i]
        by {
            if i < len {
            } else {
                assert(i == len);
            }
        }
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

        proof {
            assert(limit as int == Self::max2(
                Self::max2(r_start as int, rows as int - 1 - r_start as int),
                Self::max2(c_start as int, cols as int - 1 - c_start as int),
            ));
            assert(limit as int == Self::max_layer(rows as int, cols as int, r_start as int, c_start as int));
            assert(0 <= r_start as int);
            assert((r_start as int) < 100);
            assert(0 <= rows as int - 1 - r_start as int);
            assert((rows as int - 1 - r_start as int) < 100);
            assert(0 <= c_start as int);
            assert((c_start as int) < 100);
            assert(0 <= cols as int - 1 - c_start as int);
            assert((cols as int - 1 - c_start as int) < 100);
            assert(0 <= limit as int);
            assert((limit as int) < 100);
        }

        let mut res: Vec<Vec<i32>> = Vec::new();
        let ghost empty = res@;
        let first = vec![r_start, c_start];
        proof {
            Self::lemma_result_coords_push(empty, first);
        }
        res.push(first);
        proof {
            assert(Self::result_coords(res@) == seq![(r_start as int, c_start as int)]);
            assert(Self::spiral_coords(rows as int, cols as int, r_start as int, c_start as int, 0nat) == seq![(r_start as int, c_start as int)]);
        }

        let mut k: i32 = 1;
        while k <= limit
            invariant
                1 <= rows <= 100,
                1 <= cols <= 100,
                0 <= r_start < rows,
                0 <= c_start < cols,
                0 <= limit < 100,
                limit as int == Self::max_layer(rows as int, cols as int, r_start as int, c_start as int),
                1 <= k <= limit + 1,
                forall |i: int| 0 <= i < res@.len() ==> #[trigger] res@[i].len() == 2,
                Self::result_coords(res@) == Self::spiral_coords(rows as int, cols as int, r_start as int, c_start as int, (k - 1) as nat),
            decreases limit - k + 1,
        {
            let ghost base = Self::result_coords(res@);
            proof {
                assert(0 <= 2 * k <= 200);
            }
            let side_len = 2 * k;

            let mut i: i32 = 0;
            while i < side_len
                invariant
                    1 <= rows <= 100,
                    1 <= cols <= 100,
                    0 <= r_start < rows,
                    0 <= c_start < cols,
                    0 <= limit < 100,
                    1 <= k <= limit,
                    side_len == 2 * k,
                    0 <= i <= side_len,
                    forall |j: int| 0 <= j < res@.len() ==> #[trigger] res@[j].len() == 2,
                    Self::result_coords(res@)
                        == base + Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int),
                decreases side_len - i,
            {
                let r = r_start as i64 - k as i64 + 1 + i as i64;
                let c = c_start as i64 + k as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let ghost prev = res@;
                    let pair = vec![rr, cc];
                    proof {
                        Self::lemma_result_coords_push(prev, pair);
                    }
                    res.push(pair);
                    proof {
                        Self::lemma_east_segment_extend(r_start as int, c_start as int, k as int, i as int);
                        Self::lemma_filter_append(Self::east_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int, (r as int, c as int));
                        assert(Self::in_bounds(rows as int, cols as int, r as int, c as int));
                        assert(Self::result_coords(prev) == base + Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int));
                        assert(Self::result_coords(res@)
                            == base + Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int).push((r as int, c as int)));
                        assert(Self::result_coords(res@)
                            == base + Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, i as int + 1), rows as int, cols as int));
                    }
                } else {
                    proof {
                        Self::lemma_east_segment_extend(r_start as int, c_start as int, k as int, i as int);
                        Self::lemma_filter_append(Self::east_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int, (r as int, c as int));
                        assert(!Self::in_bounds(rows as int, cols as int, r as int, c as int));
                        assert(Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, i as int + 1), rows as int, cols as int)
                            == Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int));
                    }
                }
                i += 1;
            }

            proof {
                assert(Self::result_coords(res@)
                    == base + Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int));
            }

            let ghost after_east = Self::result_coords(res@);
            i = 0;
            while i < side_len
                invariant
                    1 <= rows <= 100,
                    1 <= cols <= 100,
                    0 <= r_start < rows,
                    0 <= c_start < cols,
                    0 <= limit < 100,
                    1 <= k <= limit,
                    side_len == 2 * k,
                    0 <= i <= side_len,
                    forall |j: int| 0 <= j < res@.len() ==> #[trigger] res@[j].len() == 2,
                    Self::result_coords(res@)
                        == after_east + Self::filter_in_bounds(Self::south_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int),
                decreases side_len - i,
            {
                let r = r_start as i64 + k as i64;
                let c = c_start as i64 + k as i64 - 1 - i as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let ghost prev = res@;
                    let pair = vec![rr, cc];
                    proof {
                        Self::lemma_result_coords_push(prev, pair);
                    }
                    res.push(pair);
                    proof {
                        Self::lemma_south_segment_extend(r_start as int, c_start as int, k as int, i as int);
                        Self::lemma_filter_append(Self::south_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int, (r as int, c as int));
                        assert(Self::in_bounds(rows as int, cols as int, r as int, c as int));
                        assert(Self::result_coords(prev) == after_east + Self::filter_in_bounds(Self::south_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int));
                        assert(Self::result_coords(res@)
                            == after_east + Self::filter_in_bounds(Self::south_segment(r_start as int, c_start as int, k as int, i as int + 1), rows as int, cols as int));
                    }
                } else {
                    proof {
                        Self::lemma_south_segment_extend(r_start as int, c_start as int, k as int, i as int);
                        Self::lemma_filter_append(Self::south_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int, (r as int, c as int));
                        assert(!Self::in_bounds(rows as int, cols as int, r as int, c as int));
                        assert(Self::filter_in_bounds(Self::south_segment(r_start as int, c_start as int, k as int, i as int + 1), rows as int, cols as int)
                            == Self::filter_in_bounds(Self::south_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int));
                    }
                }
                i += 1;
            }

            proof {
                assert(Self::result_coords(res@)
                    == after_east + Self::filter_in_bounds(Self::south_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int));
            }

            let ghost after_south = Self::result_coords(res@);
            i = 0;
            while i < side_len
                invariant
                    1 <= rows <= 100,
                    1 <= cols <= 100,
                    0 <= r_start < rows,
                    0 <= c_start < cols,
                    0 <= limit < 100,
                    1 <= k <= limit,
                    side_len == 2 * k,
                    0 <= i <= side_len,
                    forall |j: int| 0 <= j < res@.len() ==> #[trigger] res@[j].len() == 2,
                    Self::result_coords(res@)
                        == after_south + Self::filter_in_bounds(Self::west_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int),
                decreases side_len - i,
            {
                let r = r_start as i64 + k as i64 - 1 - i as i64;
                let c = c_start as i64 - k as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let ghost prev = res@;
                    let pair = vec![rr, cc];
                    proof {
                        Self::lemma_result_coords_push(prev, pair);
                    }
                    res.push(pair);
                    proof {
                        Self::lemma_west_segment_extend(r_start as int, c_start as int, k as int, i as int);
                        Self::lemma_filter_append(Self::west_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int, (r as int, c as int));
                        assert(Self::in_bounds(rows as int, cols as int, r as int, c as int));
                        assert(Self::result_coords(prev) == after_south + Self::filter_in_bounds(Self::west_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int));
                        assert(Self::result_coords(res@)
                            == after_south + Self::filter_in_bounds(Self::west_segment(r_start as int, c_start as int, k as int, i as int + 1), rows as int, cols as int));
                    }
                } else {
                    proof {
                        Self::lemma_west_segment_extend(r_start as int, c_start as int, k as int, i as int);
                        Self::lemma_filter_append(Self::west_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int, (r as int, c as int));
                        assert(!Self::in_bounds(rows as int, cols as int, r as int, c as int));
                        assert(Self::filter_in_bounds(Self::west_segment(r_start as int, c_start as int, k as int, i as int + 1), rows as int, cols as int)
                            == Self::filter_in_bounds(Self::west_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int));
                    }
                }
                i += 1;
            }

            proof {
                assert(Self::result_coords(res@)
                    == after_south + Self::filter_in_bounds(Self::west_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int));
            }

            let ghost after_west = Self::result_coords(res@);
            i = 0;
            while i < side_len
                invariant
                    1 <= rows <= 100,
                    1 <= cols <= 100,
                    0 <= r_start < rows,
                    0 <= c_start < cols,
                    0 <= limit < 100,
                    1 <= k <= limit,
                    side_len == 2 * k,
                    0 <= i <= side_len,
                    forall |j: int| 0 <= j < res@.len() ==> #[trigger] res@[j].len() == 2,
                    Self::result_coords(res@)
                        == after_west + Self::filter_in_bounds(Self::north_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int),
                decreases side_len - i,
            {
                let r = r_start as i64 - k as i64;
                let c = c_start as i64 - k as i64 + 1 + i as i64;
                if 0 <= r && r < rows as i64 && 0 <= c && c < cols as i64 {
                    let rr = r as i32;
                    let cc = c as i32;
                    let ghost prev = res@;
                    let pair = vec![rr, cc];
                    proof {
                        Self::lemma_result_coords_push(prev, pair);
                    }
                    res.push(pair);
                    proof {
                        Self::lemma_north_segment_extend(r_start as int, c_start as int, k as int, i as int);
                        Self::lemma_filter_append(Self::north_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int, (r as int, c as int));
                        assert(Self::in_bounds(rows as int, cols as int, r as int, c as int));
                        assert(Self::result_coords(prev) == after_west + Self::filter_in_bounds(Self::north_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int));
                        assert(Self::result_coords(res@)
                            == after_west + Self::filter_in_bounds(Self::north_segment(r_start as int, c_start as int, k as int, i as int + 1), rows as int, cols as int));
                    }
                } else {
                    proof {
                        Self::lemma_north_segment_extend(r_start as int, c_start as int, k as int, i as int);
                        Self::lemma_filter_append(Self::north_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int, (r as int, c as int));
                        assert(!Self::in_bounds(rows as int, cols as int, r as int, c as int));
                        assert(Self::filter_in_bounds(Self::north_segment(r_start as int, c_start as int, k as int, i as int + 1), rows as int, cols as int)
                            == Self::filter_in_bounds(Self::north_segment(r_start as int, c_start as int, k as int, i as int), rows as int, cols as int));
                    }
                }
                i += 1;
            }

            proof {
                assert(Self::result_coords(res@)
                    == after_west + Self::filter_in_bounds(Self::north_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int));
                assert(base == Self::spiral_coords(rows as int, cols as int, r_start as int, c_start as int, (k - 1) as nat));
                assert(Self::result_coords(res@)
                    == base
                    + Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int)
                    + Self::filter_in_bounds(Self::south_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int)
                    + Self::filter_in_bounds(Self::west_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int)
                    + Self::filter_in_bounds(Self::north_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int));
                assert(Self::ring_coords(rows as int, cols as int, r_start as int, c_start as int, k as int)
                    == Self::filter_in_bounds(Self::east_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int)
                    + Self::filter_in_bounds(Self::south_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int)
                    + Self::filter_in_bounds(Self::west_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int)
                    + Self::filter_in_bounds(Self::north_segment(r_start as int, c_start as int, k as int, 2 * k as int), rows as int, cols as int));
                assert(Self::spiral_coords(rows as int, cols as int, r_start as int, c_start as int, k as nat)
                    == Self::spiral_coords(rows as int, cols as int, r_start as int, c_start as int, (k - 1) as nat)
                        + Self::ring_coords(rows as int, cols as int, r_start as int, c_start as int, k as int));
            }
            k += 1;
        }

        proof {
            assert(k == limit + 1);
            assert(k as int - 1 == limit as int);
        }

        res
    }
}

}
