use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inside(points: Seq<Seq<int>>, i: int, j: int, t: int) -> bool {
        &&& points[i][0] <= points[t][0]
        &&& points[t][0] <= points[j][0]
        &&& points[j][1] <= points[t][1]
        &&& points[t][1] <= points[i][1]
    }

    pub open spec fn valid_pair(points: Seq<Seq<int>>, i: int, j: int) -> bool {
        &&& i != j
        &&& points[i][0] <= points[j][0]
        &&& points[i][1] >= points[j][1]
        &&& (forall|t: int|
            0 <= t < points.len() && t != i && t != j ==> !Self::inside(points, i, j, t))
    }

    pub open spec fn count_j(points: Seq<Seq<int>>, i: int, jend: int) -> int
        decreases jend,
    {
        if jend <= 0 {
            0
        } else {
            Self::count_j(points, i, jend - 1) + (if Self::valid_pair(points, i, jend - 1) {
                1int
            } else {
                0int
            })
        }
    }

    pub open spec fn count_i(points: Seq<Seq<int>>, iend: int) -> int
        decreases iend,
    {
        if iend <= 0 {
            0
        } else {
            Self::count_i(points, iend - 1) + Self::count_j(points, iend - 1, points.len() as int)
        }
    }

    pub open spec fn spec_number_of_pairs(points: Seq<Seq<int>>) -> int {
        Self::count_i(points, points.len() as int)
    }

    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= points.len() <= 1000,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len()
                ==> -1_000_000_000 <= #[trigger] points[i][0] <= 1_000_000_000
                    && -1_000_000_000 <= points[i][1] <= 1_000_000_000,
        ensures
            result as int == Self::spec_number_of_pairs(points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int))),
    {
        let n = points.len();
        let ghost gpts = points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int));
        assert(gpts.len() == n);

        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == points.len(),
                2 <= n <= 1000,
                i <= n,
                forall|k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
                gpts == points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int)),
                gpts.len() == n,
                ans as int == Self::count_i(gpts, i as int),
                0 <= ans as int <= (i as int) * (n as int),
            decreases n - i,
        {
            assert(points[i as int].len() == 2);
            let ax = points[i][0];
            let ay = points[i][1];
            assert(gpts[i as int][0] == ax as int);
            assert(gpts[i as int][1] == ay as int);

            let mut j: usize = 0;
            while j < n
                invariant
                    n == points.len(),
                    2 <= n <= 1000,
                    i < n,
                    j <= n,
                    forall|k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
                    gpts == points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int)),
                    gpts.len() == n,
                    gpts[i as int][0] == ax as int,
                    gpts[i as int][1] == ay as int,
                    ans as int == Self::count_i(gpts, i as int) + Self::count_j(gpts, i as int, j as int),
                    0 <= ans as int <= (i as int) * (n as int) + (j as int),
                decreases n - j,
            {
                let ghost ans0 = ans as int;
                assert((i as int) * (n as int) + (j as int) < 1_000_001) by (nonlinear_arith)
                    requires
                        i as int >= 0,
                        (i as int) < (n as int),
                        j as int >= 0,
                        (j as int) < (n as int),
                        n as int <= 1000,
                ;

                if i != j {
                    assert(points[j as int].len() == 2);
                    let bx = points[j][0];
                    let by = points[j][1];
                    assert(gpts[j as int][0] == bx as int);
                    assert(gpts[j as int][1] == by as int);

                    if ax <= bx && ay >= by {
                        let mut blocked = false;
                        let mut t: usize = 0;
                        while t < n
                            invariant
                                n == points.len(),
                                2 <= n <= 1000,
                                i < n,
                                j < n,
                                i != j,
                                t <= n,
                                forall|k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
                                gpts == points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int)),
                                gpts.len() == n,
                                gpts[i as int][0] == ax as int,
                                gpts[i as int][1] == ay as int,
                                gpts[j as int][0] == bx as int,
                                gpts[j as int][1] == by as int,
                                blocked == (exists|tt: int|
                                    0 <= tt < t as int && tt != i as int && tt != j as int
                                        && Self::inside(gpts, i as int, j as int, tt)),
                            decreases n - t,
                        {
                            if t != i && t != j {
                                assert(points[t as int].len() == 2);
                                let x = points[t][0];
                                let y = points[t][1];
                                assert(gpts[t as int][0] == x as int);
                                assert(gpts[t as int][1] == y as int);
                                if ax <= x && x <= bx && by <= y && y <= ay {
                                    assert(Self::inside(gpts, i as int, j as int, t as int));
                                    blocked = true;
                                }
                            }
                            assert forall|tt: int|
                                0 <= tt < (t + 1) as int && tt != i as int && tt != j as int
                                    && Self::inside(gpts, i as int, j as int, tt)
                                implies (blocked || tt < t as int) by {
                                if tt == t as int {
                                    assert(Self::inside(gpts, i as int, j as int, tt));
                                }
                            }
                            t = t + 1;
                        }

                        assert(!blocked ==> Self::valid_pair(gpts, i as int, j as int)) by {
                            if !blocked {
                                assert forall|tt: int|
                                    0 <= tt < gpts.len() && tt != i as int && tt != j as int
                                    implies !Self::inside(gpts, i as int, j as int, tt) by {
                                }
                            }
                        }
                        assert(blocked ==> !Self::valid_pair(gpts, i as int, j as int));

                        if !blocked {
                            ans = ans + 1;
                        }
                    } else {
                        assert(!Self::valid_pair(gpts, i as int, j as int));
                    }
                } else {
                    assert(!Self::valid_pair(gpts, i as int, j as int));
                }

                assert(ans as int == ans0 + (if Self::valid_pair(gpts, i as int, j as int) {
                    1int
                } else {
                    0int
                }));
                assert(Self::count_j(gpts, i as int, (j + 1) as int) == Self::count_j(gpts, i as int, j as int)
                    + (if Self::valid_pair(gpts, i as int, j as int) { 1int } else { 0int }));
                j = j + 1;
            }
            assert(Self::count_i(gpts, (i + 1) as int) == Self::count_i(gpts, i as int)
                + Self::count_j(gpts, i as int, n as int));
            assert((i as int + 1) * (n as int) == (i as int) * (n as int) + (n as int))
                by (nonlinear_arith);
            i = i + 1;
        }
        assert(ans as int == Self::count_i(gpts, n as int));
        ans
    }
}

}