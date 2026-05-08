use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_upper_bound;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_i2min(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

pub open spec fn spec_min_first_i(s: Seq<i64>, i: int) -> int
    recommends
        s.len() == 4,
        1 <= i <= 4,
{
    if i == 1 {
        s[0] as int
    } else if i == 2 {
        spec_i2min(s[0] as int, s[1] as int)
    } else if i == 3 {
        spec_i2min(spec_i2min(s[0] as int, s[1] as int), s[2] as int)
    } else {
        spec_i2min(
            spec_i2min(s[0] as int, s[1] as int),
            spec_i2min(s[2] as int, s[3] as int),
        )
    }
}

pub open spec fn spec_max_first_i(s: Seq<i64>, i: int) -> int
    recommends
        s.len() == 4,
        1 <= i <= 4,
{
    if i == 1 {
        s[0] as int
    } else if i == 2 {
        spec_i2max(s[0] as int, s[1] as int)
    } else if i == 3 {
        spec_i2max(spec_i2max(s[0] as int, s[1] as int), s[2] as int)
    } else {
        spec_i2max(
            spec_i2max(s[0] as int, s[1] as int),
            spec_i2max(s[2] as int, s[3] as int),
        )
    }
}

pub open spec fn spec_axis_span(s: Seq<i64>) -> int
    recommends
        s.len() == 4,
{
    spec_max_first_i(s, 4) - spec_min_first_i(s, 4)
}

proof fn lemma_min_first_i_succ(s: Seq<i64>, i: int)
    requires
        s.len() == 4,
        1 <= i < 4,
    ensures
        spec_min_first_i(s, i + 1) == spec_i2min(spec_min_first_i(s, i), s[i] as int),
{
}

proof fn lemma_max_first_i_succ(s: Seq<i64>, i: int)
    requires
        s.len() == 4,
        1 <= i < 4,
    ensures
        spec_max_first_i(s, i + 1) == spec_i2max(spec_max_first_i(s, i), s[i] as int),
{
}

proof fn lemma_axis_span_from_corners(s: Seq<i64>, lo: i64, hi: i64)
    requires
        s.len() == 4,
        (lo as int) == spec_min_first_i(s, 4),
        (hi as int) == spec_max_first_i(s, 4),
    ensures
        spec_axis_span(s) == (hi - lo) as int,
{
}

proof fn lemma_corner_min_max_in_range(s: Seq<i64>, lo: i64, hi: i64)
    requires
        s.len() == 4,
        forall|k: int| 0 <= k < 4 ==> -1000 <= (#[trigger] s[k] as int) && (s[k] as int) <= 1000,
        (lo as int) == spec_min_first_i(s, 4),
        (hi as int) == spec_max_first_i(s, 4),
    ensures
        -1000 <= (lo as int) && (lo as int) <= 1000,
        -1000 <= (hi as int) && (hi as int) <= 1000,
        (hi as int) - (lo as int) <= 2000,
        0 <= (hi as int) - (lo as int),
{
    assert(-1000 <= (s[0] as int) && (s[0] as int) <= 1000);
    assert(-1000 <= (s[1] as int) && (s[1] as int) <= 1000);
    assert(-1000 <= (s[2] as int) && (s[2] as int) <= 1000);
    assert(-1000 <= (s[3] as int) && (s[3] as int) <= 1000);
    assert((lo as int) <= (s[0] as int));
    assert((lo as int) <= (s[1] as int));
    assert((lo as int) <= (s[2] as int));
    assert((lo as int) <= (s[3] as int));
    assert((s[0] as int) <= (hi as int));
    assert((s[1] as int) <= (hi as int));
    assert((s[2] as int) <= (hi as int));
    assert((s[3] as int) <= (hi as int));
}

impl Solution {
    pub fn axis_aligned_square_area(xs: Vec<i64>, ys: Vec<i64>) -> (res: i64)
        requires
            xs.len() == 4,
            ys.len() == 4,
            forall|j: int|
                0 <= j < 4 ==> -1000 <= (#[trigger] xs[j] as int) && (xs[j] as int) <= 1000 && -1000 <= (ys[j] as int) && (ys[j] as int) <= 1000,
            spec_axis_span(xs@) == spec_axis_span(ys@),
            spec_axis_span(xs@) > 0,
        ensures
            res as int == spec_axis_span(xs@) * spec_axis_span(ys@),
    {
        let mut min_x = xs[0];
        let mut max_x = xs[0];
        let mut i = 1usize;
        while i < 4
            invariant
                xs.len() == 4,
                1 <= i <= 4,
                (min_x as int) == spec_min_first_i(xs@, i as int),
                (max_x as int) == spec_max_first_i(xs@, i as int),
            decreases 4 - i,
        {
            proof {
                assert((i as int) < 4);
                assert(1 <= (i as int));
                lemma_min_first_i_succ(xs@, i as int);
                lemma_max_first_i_succ(xs@, i as int);
            }
            if xs[i] < min_x {
                min_x = xs[i];
            }
            if xs[i] > max_x {
                max_x = xs[i];
            }
            proof {
                assert(spec_min_first_i(xs@, i as int + 1) == spec_i2min(spec_min_first_i(xs@, i as int), xs@[i as int] as int));
                assert(spec_max_first_i(xs@, i as int + 1) == spec_i2max(spec_max_first_i(xs@, i as int), xs@[i as int] as int));
                assert((min_x as int) == spec_min_first_i(xs@, i as int + 1));
                assert((max_x as int) == spec_max_first_i(xs@, i as int + 1));
            }
            i = i + 1;
        }
        proof {
            assert(i == 4);
            assert((min_x as int) == spec_min_first_i(xs@, 4));
            assert((max_x as int) == spec_max_first_i(xs@, 4));
        }
        let mut min_y = ys[0];
        let mut max_y = ys[0];
        let mut j = 1usize;
        while j < 4
            invariant
                ys.len() == 4,
                1 <= j <= 4,
                (min_y as int) == spec_min_first_i(ys@, j as int),
                (max_y as int) == spec_max_first_i(ys@, j as int),
            decreases 4 - j,
        {
            proof {
                assert((j as int) < 4);
                assert(1 <= (j as int));
                lemma_min_first_i_succ(ys@, j as int);
                lemma_max_first_i_succ(ys@, j as int);
            }
            if ys[j] < min_y {
                min_y = ys[j];
            }
            if ys[j] > max_y {
                max_y = ys[j];
            }
            proof {
                assert(spec_min_first_i(ys@, j as int + 1) == spec_i2min(spec_min_first_i(ys@, j as int), ys@[j as int] as int));
                assert(spec_max_first_i(ys@, j as int + 1) == spec_i2max(spec_max_first_i(ys@, j as int), ys@[j as int] as int));
                assert((min_y as int) == spec_min_first_i(ys@, j as int + 1));
                assert((max_y as int) == spec_max_first_i(ys@, j as int + 1));
            }
            j = j + 1;
        }
        proof {
            assert(j == 4);
            assert((min_y as int) == spec_min_first_i(ys@, 4));
            assert((max_y as int) == spec_max_first_i(ys@, 4));
            lemma_axis_span_from_corners(xs@, min_x, max_x);
            lemma_axis_span_from_corners(ys@, min_y, max_y);
            assert(spec_axis_span(xs@) == (max_x - min_x) as int);
            assert(spec_axis_span(ys@) == (max_y - min_y) as int);
            assert((max_x - min_x) as int == (max_y - min_y) as int);
            assert(((max_x - min_x) * (max_y - min_y)) as int == spec_axis_span(xs@) * spec_axis_span(ys@));
        }
        let sx = max_x - min_x;
        let sy = max_y - min_y;
        proof {
            lemma_corner_min_max_in_range(xs@, min_x, max_x);
            lemma_corner_min_max_in_range(ys@, min_y, max_y);
            let xi = sx as int;
            let yi = sy as int;
            assert(xi == (max_x - min_x) as int);
            assert(yi == (max_y - min_y) as int);
            assert(0 <= xi && xi <= 2000);
            assert(0 <= yi && yi <= 2000);
            lemma_mul_upper_bound(xi, 2000, yi, 2000);
            assert(xi * yi <= 2000 * 2000);
            assert(2000 * 2000 == 4000000);
            assert(xi * yi <= 4000000);
            assert(xi * yi < 0x7fff_ffff_ffff_ffff);
            assert((sx * sy) as int == xi * yi);
            assert((sx * sy) as int == spec_axis_span(xs@) * spec_axis_span(ys@));
        }
        sx * sy
    }
}

}
