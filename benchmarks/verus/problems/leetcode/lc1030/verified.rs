use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_spec(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn dist_spec(r: int, c: int, rc: int, cc: int) -> int {
        Self::abs_spec(r - rc) + Self::abs_spec(c - cc)
    }

    pub open spec fn max_dist_spec(rows: int, cols: int, rc: int, cc: int) -> int {
        (if rc >= rows - 1 - rc { rc } else { rows - 1 - rc })
        + (if cc >= cols - 1 - cc { cc } else { cols - 1 - cc })
    }

    pub open spec fn cell_covered(result: Seq<Vec<i32>>, r: int, c: int) -> bool {
        exists|k: int| 0 <= k < result.len() && result[k][0] as int == r && result[k][1] as int == c
    }

    pub open spec fn count_eq_row(rc: int, cc: int, d: int, r: int, c_end: int) -> int
        decreases c_end,
    {
        if c_end <= 0 { 0 }
        else {
            Self::count_eq_row(rc, cc, d, r, c_end - 1)
            + if Self::dist_spec(r, c_end - 1, rc, cc) == d { 1int } else { 0 }
        }
    }

    pub open spec fn count_eq_rows(cols: int, rc: int, cc: int, d: int, r_end: int) -> int
        decreases r_end,
    {
        if r_end <= 0 { 0 }
        else {
            Self::count_eq_rows(cols, rc, cc, d, r_end - 1)
            + Self::count_eq_row(rc, cc, d, r_end - 1, cols)
        }
    }

    pub open spec fn count_below(r_end: int, cols: int, rc: int, cc: int, d_end: int) -> int
        decreases d_end,
    {
        if d_end <= 0 { 0 }
        else {
            Self::count_below(r_end, cols, rc, cc, d_end - 1)
            + Self::count_eq_rows(cols, rc, cc, d_end - 1, r_end)
        }
    }

    pub open spec fn count_lt_row(rc: int, cc: int, r: int, c_end: int, d_end: int) -> int
        decreases c_end,
    {
        if c_end <= 0 { 0 }
        else {
            Self::count_lt_row(rc, cc, r, c_end - 1, d_end)
            + if Self::dist_spec(r, c_end - 1, rc, cc) < d_end { 1int } else { 0 }
        }
    }

    pub open spec fn count_lt_total(r_end: int, cols: int, rc: int, cc: int, d_end: int) -> int
        decreases r_end,
    {
        if r_end <= 0 { 0 }
        else {
            Self::count_lt_total(r_end - 1, cols, rc, cc, d_end)
            + Self::count_lt_row(rc, cc, r_end - 1, cols, d_end)
        }
    }

    pub open spec fn cell_before(d: int, r_scan: int, c_scan: int, r: int, c: int, rc: int, cc: int) -> bool {
        let cd = Self::dist_spec(r, c, rc, cc);
        cd < d || (cd == d && (r < r_scan || (r == r_scan && c < c_scan)))
    }

    proof fn lemma_dist_bounded(rows: int, cols: int, rc: int, cc: int, r: int, c: int)
        requires
            1 <= rows, 1 <= cols,
            0 <= rc < rows, 0 <= cc < cols,
            0 <= r < rows, 0 <= c < cols,
        ensures
            Self::dist_spec(r, c, rc, cc) <= Self::max_dist_spec(rows, cols, rc, cc),
    {
    }

    proof fn lemma_count_row_split(rc: int, cc: int, r: int, c_end: int, d_end: int)
        ensures
            Self::count_lt_row(rc, cc, r, c_end, d_end + 1)
            == Self::count_lt_row(rc, cc, r, c_end, d_end)
            + Self::count_eq_row(rc, cc, d_end, r, c_end),
        decreases c_end,
    {
        if c_end > 0 {
            Self::lemma_count_row_split(rc, cc, r, c_end - 1, d_end);
        }
    }

    proof fn lemma_count_total_split(r_end: int, cols: int, rc: int, cc: int, d_end: int)
        ensures
            Self::count_lt_total(r_end, cols, rc, cc, d_end + 1)
            == Self::count_lt_total(r_end, cols, rc, cc, d_end)
            + Self::count_eq_rows(cols, rc, cc, d_end, r_end),
        decreases r_end,
    {
        if r_end > 0 {
            Self::lemma_count_total_split(r_end - 1, cols, rc, cc, d_end);
            Self::lemma_count_row_split(rc, cc, r_end - 1, cols, d_end);
        }
    }

    proof fn lemma_count_lt_row_zero(rc: int, cc: int, r: int, c_end: int)
        requires c_end >= 0,
        ensures Self::count_lt_row(rc, cc, r, c_end, 0) == 0,
        decreases c_end,
    {
        if c_end > 0 {
            Self::lemma_count_lt_row_zero(rc, cc, r, c_end - 1);
        }
    }

    proof fn lemma_count_lt_total_zero(r_end: int, cols: int, rc: int, cc: int)
        requires r_end >= 0, cols >= 0,
        ensures Self::count_lt_total(r_end, cols, rc, cc, 0) == 0,
        decreases r_end,
    {
        if r_end > 0 {
            Self::lemma_count_lt_total_zero(r_end - 1, cols, rc, cc);
            Self::lemma_count_lt_row_zero(rc, cc, r_end - 1, cols);
        }
    }

    proof fn lemma_count_equal(r_end: int, cols: int, rc: int, cc: int, d_end: int)
        requires d_end >= 0, r_end >= 0, cols >= 0,
        ensures
            Self::count_lt_total(r_end, cols, rc, cc, d_end) == Self::count_below(r_end, cols, rc, cc, d_end),
        decreases d_end,
    {
        if d_end > 0 {
            Self::lemma_count_equal(r_end, cols, rc, cc, d_end - 1);
            Self::lemma_count_total_split(r_end, cols, rc, cc, d_end - 1);
        } else {
            Self::lemma_count_lt_total_zero(r_end, cols, rc, cc);
        }
    }

    proof fn lemma_count_lt_row_full(rows: int, cols: int, rc: int, cc: int, r: int, c_end: int, d_end: int)
        requires
            1 <= rows, 1 <= cols,
            0 <= rc < rows, 0 <= cc < cols,
            0 <= r < rows, 0 <= c_end <= cols,
            d_end > Self::max_dist_spec(rows, cols, rc, cc),
        ensures
            Self::count_lt_row(rc, cc, r, c_end, d_end) == c_end,
        decreases c_end,
    {
        if c_end > 0 {
            Self::lemma_count_lt_row_full(rows, cols, rc, cc, r, c_end - 1, d_end);
            Self::lemma_dist_bounded(rows, cols, rc, cc, r, c_end - 1);
        }
    }

    proof fn lemma_count_lt_total_full(rows: int, cols: int, rc: int, cc: int, r_end: int, d_end: int)
        requires
            1 <= rows, 1 <= cols,
            0 <= rc < rows, 0 <= cc < cols,
            0 <= r_end <= rows,
            d_end > Self::max_dist_spec(rows, cols, rc, cc),
        ensures
            Self::count_lt_total(r_end, cols, rc, cc, d_end) == r_end * cols,
        decreases r_end,
    {
        if r_end > 0 {
            Self::lemma_count_lt_total_full(rows, cols, rc, cc, r_end - 1, d_end);
            Self::lemma_count_lt_row_full(rows, cols, rc, cc, r_end - 1, cols, d_end);
            assert(Self::count_lt_total(r_end, cols, rc, cc, d_end)
                == Self::count_lt_total(r_end - 1, cols, rc, cc, d_end)
                + Self::count_lt_row(rc, cc, r_end - 1, cols, d_end));
            assert(Self::count_lt_total(r_end, cols, rc, cc, d_end) == (r_end - 1) * cols + cols);
            assert((r_end - 1) * cols + cols == r_end * cols) by (nonlinear_arith)
                requires r_end >= 1, cols >= 1;
        } else {
            assert(r_end == 0);
            assert(Self::count_lt_total(0int, cols, rc, cc, d_end) == 0int);
        }
    }

    pub fn all_cells_dist_order(rows: i32, cols: i32, r_center: i32, c_center: i32) -> (result: Vec<Vec<i32>>)
        requires
            1 <= rows <= 100,
            1 <= cols <= 100,
            0 <= r_center < rows,
            0 <= c_center < cols,
        ensures
            result@.len() == rows as int * cols as int,
            forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i]).len() == 2,
            forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                0 <= result@[i][0] < rows && 0 <= result@[i][1] < cols,
            forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() - 1 ==>
                Self::dist_spec(
                    result@[i][0] as int, result@[i][1] as int,
                    r_center as int, c_center as int,
                ) <= Self::dist_spec(
                    result@[i + 1][0] as int, result@[i + 1][1] as int,
                    r_center as int, c_center as int,
                ),
            forall|r: int, c: int| 0 <= r < rows as int && 0 <= c < cols as int ==>
                (#[trigger] Self::cell_covered(result@, r, c)),
    {
        let ghost rc = r_center as int;
        let ghost cc = c_center as int;

        let max_r_dist = if r_center > rows - 1 - r_center { r_center } else { rows - 1 - r_center };
        let max_c_dist = if c_center > cols - 1 - c_center { c_center } else { cols - 1 - c_center };
        let max_dist = max_r_dist + max_c_dist;

        let mut result: Vec<Vec<i32>> = Vec::new();
        let ghost mut indices: Seq<Seq<int>> = Seq::new(rows as nat, |_r: int| Seq::new(cols as nat, |_c: int| -1int));

        let mut d: i32 = 0;
        while d <= max_dist
            invariant
                0 <= d <= max_dist + 1,
                0 <= max_dist <= 198,
                max_dist as int == Self::max_dist_spec(rows as int, cols as int, rc, cc),
                1 <= rows <= 100,
                1 <= cols <= 100,
                0 <= r_center < rows,
                0 <= c_center < cols,
                rc == r_center as int,
                cc == c_center as int,
                result@.len() as int == Self::count_below(rows as int, cols as int, rc, cc, d as int),
                forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i]).len() == 2,
                forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                    0 <= result@[i][0] < rows && 0 <= result@[i][1] < cols,
                forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() - 1 ==>
                    Self::dist_spec(
                        result@[i][0] as int, result@[i][1] as int, rc, cc,
                    ) <= Self::dist_spec(
                        result@[i + 1][0] as int, result@[i + 1][1] as int, rc, cc,
                    ),
                forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                    Self::dist_spec(result@[i][0] as int, result@[i][1] as int, rc, cc) < d as int,
                indices.len() == rows as int,
                forall|rp: int| 0 <= rp < rows as int ==> (#[trigger] indices[rp]).len() == cols as int,
                forall|rp: int, cp: int| 0 <= rp < rows as int && 0 <= cp < cols as int
                    && Self::dist_spec(rp, cp, rc, cc) < d as int ==>
                    0 <= #[trigger] indices[rp][cp] < result@.len() as int
                    && result@[indices[rp][cp] as int][0] as int == rp
                    && result@[indices[rp][cp] as int][1] as int == cp,
                forall|rp: int, cp: int| 0 <= rp < rows as int && 0 <= cp < cols as int
                    && Self::dist_spec(rp, cp, rc, cc) >= d as int ==>
                    #[trigger] indices[rp][cp] == -1int,
            decreases max_dist - d + 1,
        {
            let mut r: i32 = 0;
            while r < rows
                invariant
                    0 <= d <= max_dist,
                    0 <= r <= rows,
                    0 <= max_dist <= 198,
                    max_dist as int == Self::max_dist_spec(rows as int, cols as int, rc, cc),
                    1 <= rows <= 100,
                    1 <= cols <= 100,
                    0 <= r_center < rows,
                    0 <= c_center < cols,
                    rc == r_center as int,
                    cc == c_center as int,
                    result@.len() as int == Self::count_below(rows as int, cols as int, rc, cc, d as int)
                        + Self::count_eq_rows(cols as int, rc, cc, d as int, r as int),
                    forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i]).len() == 2,
                    forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                        0 <= result@[i][0] < rows && 0 <= result@[i][1] < cols,
                    forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() - 1 ==>
                        Self::dist_spec(
                            result@[i][0] as int, result@[i][1] as int, rc, cc,
                        ) <= Self::dist_spec(
                            result@[i + 1][0] as int, result@[i + 1][1] as int, rc, cc,
                        ),
                    forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                        Self::dist_spec(result@[i][0] as int, result@[i][1] as int, rc, cc) <= d as int,
                    result@.len() > 0 && d > 0 ==>
                        Self::dist_spec(result@[result@.len() - 1][0] as int, result@[result@.len() - 1][1] as int, rc, cc) <= d as int,
                    indices.len() == rows as int,
                    forall|rp: int| 0 <= rp < rows as int ==> (#[trigger] indices[rp]).len() == cols as int,
                    forall|rp: int, cp: int| 0 <= rp < rows as int && 0 <= cp < cols as int
                        && Self::cell_before(d as int, r as int, 0, rp, cp, rc, cc) ==>
                        0 <= #[trigger] indices[rp][cp] < result@.len() as int
                        && result@[indices[rp][cp] as int][0] as int == rp
                        && result@[indices[rp][cp] as int][1] as int == cp,
                    forall|rp: int, cp: int| 0 <= rp < rows as int && 0 <= cp < cols as int
                        && !Self::cell_before(d as int, r as int, 0, rp, cp, rc, cc) ==>
                        #[trigger] indices[rp][cp] == -1int,
                decreases rows - r,
            {
                let mut c: i32 = 0;
                while c < cols
                    invariant
                        0 <= d <= max_dist,
                        0 <= r < rows,
                        0 <= c <= cols,
                        0 <= max_dist <= 198,
                        max_dist as int == Self::max_dist_spec(rows as int, cols as int, rc, cc),
                        1 <= rows <= 100,
                        1 <= cols <= 100,
                        0 <= r_center < rows,
                        0 <= c_center < cols,
                        rc == r_center as int,
                        cc == c_center as int,
                        result@.len() as int == Self::count_below(rows as int, cols as int, rc, cc, d as int)
                            + Self::count_eq_rows(cols as int, rc, cc, d as int, r as int)
                            + Self::count_eq_row(rc, cc, d as int, r as int, c as int),
                        forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i]).len() == 2,
                        forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                            0 <= result@[i][0] < rows && 0 <= result@[i][1] < cols,
                        forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() - 1 ==>
                            Self::dist_spec(
                                result@[i][0] as int, result@[i][1] as int, rc, cc,
                            ) <= Self::dist_spec(
                                result@[i + 1][0] as int, result@[i + 1][1] as int, rc, cc,
                            ),
                        forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                            Self::dist_spec(result@[i][0] as int, result@[i][1] as int, rc, cc) <= d as int,
                        indices.len() == rows as int,
                        forall|rp: int| 0 <= rp < rows as int ==> (#[trigger] indices[rp]).len() == cols as int,
                        forall|rp: int, cp: int| 0 <= rp < rows as int && 0 <= cp < cols as int
                            && Self::cell_before(d as int, r as int, c as int, rp, cp, rc, cc) ==>
                            0 <= #[trigger] indices[rp][cp] < result@.len() as int
                            && result@[indices[rp][cp] as int][0] as int == rp
                            && result@[indices[rp][cp] as int][1] as int == cp,
                        forall|rp: int, cp: int| 0 <= rp < rows as int && 0 <= cp < cols as int
                            && !Self::cell_before(d as int, r as int, c as int, rp, cp, rc, cc) ==>
                            #[trigger] indices[rp][cp] == -1int,
                    decreases cols - c,
                {
                    let rd = if r >= r_center { r - r_center } else { r_center - r };
                    let cd = if c >= c_center { c - c_center } else { c_center - c };

                    proof {
                        assert(rd as int == Self::abs_spec(r as int - rc));
                        assert(cd as int == Self::abs_spec(c as int - cc));
                        assert((rd + cd) as int == Self::dist_spec(r as int, c as int, rc, cc));
                    }

                    if rd + cd == d {
                        let ghost old_len = result@.len() as int;
                        let ghost old_result = result@;

                        let mut cell: Vec<i32> = Vec::new();
                        cell.push(r);
                        cell.push(c);

                        proof {
                            assert(cell@.len() == 2);
                            assert(cell[0] == r);
                            assert(cell[1] == c);
                            if old_len > 0 {
                                assert(Self::dist_spec(result@[old_len - 1][0] as int, result@[old_len - 1][1] as int, rc, cc) <= d as int);
                                assert(Self::dist_spec(r as int, c as int, rc, cc) == d as int);
                            }
                        }

                        result.push(cell);

                        proof {
                            assert(result@.len() == old_len + 1);
                            assert(result@[old_len] == cell);
                            assert(result@[old_len].len() == 2);
                            assert(result@[old_len][0] == r);
                            assert(result@[old_len][1] == c);

                            assert forall|i: int| #![auto] 0 <= i < old_len implies
                                result@[i] == old_result[i]
                            by {}

                            if old_len > 0 {
                                let prev_idx = old_len - 1;
                                assert(Self::dist_spec(result@[prev_idx][0] as int, result@[prev_idx][1] as int, rc, cc) <= d as int);
                                assert(Self::dist_spec(result@[old_len][0] as int, result@[old_len][1] as int, rc, cc) == d as int);
                            }

                            let ghost old_indices = indices;
                            indices = indices.update(r as int, indices[r as int].update(c as int, old_len));

                            assert(indices[r as int][c as int] == old_len);
                            assert(indices.len() == rows as int);

                            assert forall|rp: int| 0 <= rp < rows as int implies
                                (#[trigger] indices[rp]).len() == cols as int
                            by {
                                if rp == r as int {
                                    assert(indices[rp] == old_indices[r as int].update(c as int, old_len));
                                } else {
                                    assert(indices[rp] == old_indices[rp]);
                                }
                            }
                        }
                    }

                    c = c + 1;
                }
                r = r + 1;
            }
            d = d + 1;
        }

        proof {
            Self::lemma_count_equal(rows as int, cols as int, rc, cc, max_dist as int + 1);
            Self::lemma_count_lt_total_full(rows as int, cols as int, rc, cc, rows as int, max_dist as int + 1);

            assert forall|rp: int, cp: int| 0 <= rp < rows as int && 0 <= cp < cols as int
            implies (#[trigger] Self::cell_covered(result@, rp, cp))
            by {
                Self::lemma_dist_bounded(rows as int, cols as int, rc, cc, rp, cp);
                let k = indices[rp][cp];
                assert(0 <= k < result@.len() as int);
                assert(result@[k][0] as int == rp);
                assert(result@[k][1] as int == cp);
            }
        }

        result
    }
}

}
