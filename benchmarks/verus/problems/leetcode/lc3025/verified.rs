use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_upper_left(points: Seq<Vec<i32>>, i: int, j: int) -> bool {
        &&& 0 <= i < points.len()
        &&& 0 <= j < points.len()
        &&& points[i][0] <= points[j][0]
        &&& points[i][1] >= points[j][1]
    }

    pub open spec fn blocks(points: Seq<Vec<i32>>, i: int, j: int, k: int) -> bool {
        &&& 0 <= i < points.len()
        &&& 0 <= j < points.len()
        &&& 0 <= k < points.len()
        &&& k != i
        &&& k != j
        &&& points[i][0] <= points[k][0] <= points[j][0]
        &&& points[j][1] <= points[k][1] <= points[i][1]
    }

    pub open spec fn no_block_prefix(points: Seq<Vec<i32>>, i: int, j: int, end: int) -> bool
        decreases end,
    {
        if end <= 0 {
            true
        } else {
            Self::no_block_prefix(points, i, j, end - 1)
                && !Self::blocks(points, i, j, end - 1)
        }
    }

    pub open spec fn valid_pair(points: Seq<Vec<i32>>, i: int, j: int) -> bool {
        &&& i != j
        &&& Self::is_upper_left(points, i, j)
        &&& Self::no_block_prefix(points, i, j, points.len() as int)
    }

    pub open spec fn count_i_prefix(points: Seq<Vec<i32>>, i: int, end_j: int) -> int
        decreases end_j,
    {
        if end_j <= 0 {
            0
        } else {
            Self::count_i_prefix(points, i, end_j - 1)
                + if Self::valid_pair(points, i, end_j - 1) { 1int } else { 0int }
        }
    }

    pub open spec fn number_of_pairs_spec_prefix(points: Seq<Vec<i32>>, end_i: int) -> int
        decreases end_i,
    {
        if end_i <= 0 {
            0
        } else {
            Self::number_of_pairs_spec_prefix(points, end_i - 1)
                + Self::count_i_prefix(points, end_i - 1, points.len() as int)
        }
    }

    pub open spec fn number_of_pairs_spec(points: Seq<Vec<i32>>) -> int {
        Self::number_of_pairs_spec_prefix(points, points.len() as int)
    }

    proof fn lemma_count_i_prefix_bounds(points: Seq<Vec<i32>>, i: int, end_j: int)
        requires
            0 <= i < points.len(),
            0 <= end_j <= points.len(),
        ensures
            0 <= Self::count_i_prefix(points, i, end_j) <= end_j,
        decreases end_j,
    {
        if end_j > 0 {
            Self::lemma_count_i_prefix_bounds(points, i, end_j - 1);
        }
    }

    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= points.len() <= 50,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][0] <= 50,
            forall |i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][1] <= 50,
            forall |i: int, j: int| 0 <= i < j < points.len() ==> #[trigger] points[i] != #[trigger] points[j],
        ensures
            result as int == Self::number_of_pairs_spec(points@),
    {
        let n = points.len();
        let mut ans: i32 = 0;

        let mut i: usize = 0;
        while i < n
            invariant
                n == points.len(),
                2 <= n <= 50,
                0 <= i <= n,
                forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t].len() == 2,
                forall |t: int| 0 <= t < points.len() ==> 0 <= #[trigger] points[t][0],
                forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t][0] <= 50,
                forall |t: int| 0 <= t < points.len() ==> 0 <= #[trigger] points[t][1],
                forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t][1] <= 50,
                forall |a: int, b: int| 0 <= a < b < points.len() ==> #[trigger] points[a] != #[trigger] points[b],
                ans as int == Self::number_of_pairs_spec_prefix(points@, i as int),
                0 <= ans as int <= i as int * n as int,
            decreases n - i,
        {
            let ghost old_i = i as int;
            let ghost old_ans = ans as int;
            let mut j: usize = 0;
            while j < n
                invariant
                    n == points.len(),
                    2 <= n <= 50,
                    0 <= i < n,
                    0 <= j <= n,
                    i as int == old_i,
                    points[i as int].len() == 2,
                    forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t].len() == 2,
                    forall |t: int| 0 <= t < points.len() ==> 0 <= #[trigger] points[t][0],
                    forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t][0] <= 50,
                    forall |t: int| 0 <= t < points.len() ==> 0 <= #[trigger] points[t][1],
                    forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t][1] <= 50,
                    forall |a: int, b: int| 0 <= a < b < points.len() ==> #[trigger] points[a] != #[trigger] points[b],
                    old_ans == Self::number_of_pairs_spec_prefix(points@, old_i),
                    old_ans <= old_i * n as int,
                    old_i < n as int,
                    ans as int == old_ans + Self::count_i_prefix(points@, old_i, j as int),
                    0 <= ans as int <= old_ans + j as int,
                decreases n - j,
            {
                let ghost old_j = j as int;
                let mut pair_valid = false;
                if i != j {
                    proof {
                        assert(points[i as int].len() == 2);
                        assert(points[j as int].len() == 2);
                    }
                    let x1 = points[i][0];
                    let y1 = points[i][1];
                    let x2 = points[j][0];
                    let y2 = points[j][1];
                    if x1 <= x2 && y1 >= y2 {
                        let mut ok = true;
                        let mut k: usize = 0;
                        while k < n
                            invariant
                                n == points.len(),
                                0 <= i < n,
                                0 <= j < n,
                                0 <= k <= n,
                                i as int != j as int,
                                points[i as int].len() == 2,
                                points[j as int].len() == 2,
                                forall |t: int| 0 <= t < points.len() ==> #[trigger] points[t].len() == 2,
                                x1 == points[i as int][0],
                                y1 == points[i as int][1],
                                x2 == points[j as int][0],
                                y2 == points[j as int][1],
                                x1 <= x2,
                                y1 >= y2,
                                ok <==> Self::no_block_prefix(points@, i as int, j as int, k as int),
                            decreases n - k,
                        {
                            let mut is_block = false;
                            if k != i && k != j {
                                proof {
                                    assert(points[k as int].len() == 2);
                                }
                                let x3 = points[k][0];
                                let y3 = points[k][1];
                                if x1 <= x3 && x3 <= x2 && y2 <= y3 && y3 <= y1 {
                                    is_block = true;
                                }
                            }
                            ok = ok && !is_block;
                            proof {
                                assert(Self::no_block_prefix(points@, i as int, j as int, (k + 1) as int)
                                    == (Self::no_block_prefix(points@, i as int, j as int, k as int)
                                        && !Self::blocks(points@, i as int, j as int, k as int)));
                                assert(is_block == Self::blocks(points@, i as int, j as int, k as int));
                                assert(ok <==> Self::no_block_prefix(points@, i as int, j as int, (k + 1) as int));
                            }
                            k += 1;
                        }
                        pair_valid = ok;
                    }
                }
                let add: i32 = if pair_valid { 1 } else { 0 };
                proof {
                    assert(0 <= add <= 1);
                    assert(ans as int <= old_ans + old_j);
                    assert(old_j < n as int);
                    assert(old_i * n as int <= 2450) by (nonlinear_arith)
                        requires
                            0 <= old_i,
                            old_i < n as int,
                            n <= 50,
                    {
                    }
                    assert(old_ans <= 2450);
                    assert(old_j <= 49) by (nonlinear_arith)
                        requires
                            0 <= old_j,
                            old_j < n as int,
                            n <= 50,
                    {
                    }
                    assert(ans as int + add as int <= 2500);
                }
                ans += add;
                proof {
                    assert(i as int == old_i);
                    assert(j as int == old_j);
                    if pair_valid {
                        assert(Self::valid_pair(points@, old_i, old_j));
                    } else {
                        assert(!Self::valid_pair(points@, old_i, old_j));
                    }
                    assert(add as int == if Self::valid_pair(points@, old_i, old_j) { 1int } else { 0int });
                    assert(Self::count_i_prefix(points@, old_i, old_j + 1)
                        == Self::count_i_prefix(points@, old_i, old_j)
                            + if Self::valid_pair(points@, old_i, old_j) { 1int } else { 0int });
                    assert(ans as int == old_ans + Self::count_i_prefix(points@, old_i, old_j + 1));
                    assert(ans as int <= old_ans + (old_j + 1));
                }
                j += 1;
            }
            proof {
                assert(j == n);
                assert(ans as int == old_ans + Self::count_i_prefix(points@, old_i, n as int));
                Self::lemma_count_i_prefix_bounds(points@, old_i, n as int);
                assert(Self::count_i_prefix(points@, old_i, n as int) <= n as int);
                assert(ans as int <= old_ans + n as int);
                assert(old_ans <= old_i * n as int);
                assert(old_i * n as int + n as int <= (old_i + 1) * n as int) by (nonlinear_arith)
                    requires
                        old_i >= 0,
                        n >= 0,
                {
                }
                assert(Self::number_of_pairs_spec_prefix(points@, old_i + 1)
                    == Self::number_of_pairs_spec_prefix(points@, old_i)
                        + Self::count_i_prefix(points@, old_i, points@.len() as int));
                assert(ans as int == Self::number_of_pairs_spec_prefix(points@, old_i + 1));
                assert(ans as int <= (old_i + 1) * n as int);
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(ans as int == Self::number_of_pairs_spec_prefix(points@, n as int));
            assert(Self::number_of_pairs_spec(points@) == Self::number_of_pairs_spec_prefix(points@, points@.len() as int));
            assert(ans as int == Self::number_of_pairs_spec(points@));
        }
        ans
    }
}

}
