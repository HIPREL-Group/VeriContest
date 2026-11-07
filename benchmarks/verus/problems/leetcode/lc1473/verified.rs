use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;






pub open spec fn valid_coloring(houses: Seq<i32>, colors: Seq<int>, n: int) -> bool {
    houses.len() == colors.len() &&
    forall|i: int| 0 <= i < houses.len() as int ==> (
        1 <= #[trigger] colors[i] <= n &&
        (houses[i] != 0 ==> colors[i] == houses[i] as int)
    )
}


pub open spec fn count_neighborhoods(colors: Seq<int>) -> int
    decreases colors.len(),
{
    if colors.len() <= 0 {
        0
    } else if colors.len() == 1 {
        1
    } else {
        count_neighborhoods(colors.drop_last()) +
        if colors.last() != colors[colors.len() - 2] { 1int } else { 0int }
    }
}


pub open spec fn total_paint_cost(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    colors: Seq<int>,
    len: int,
) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else {
        total_paint_cost(houses, cost, colors, len - 1) +
        if houses[len - 1] != 0i32 { 0int } else { cost[len - 1]@[colors[len - 1] - 1] as int }
    }
}





pub open spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn dp_spec(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    n: int,
    i: int,
    j: int,
    k: int,
) -> int
    decreases i, 0int,
{
    if j < 1 || j > n || k < 1 || k > i + 1 {
        1_000_001int
    } else if i == 0 {
        if k != 1 {
            1_000_001int
        } else if houses[0] as int != 0 && houses[0] as int != j {
            1_000_001int
        } else if houses[0] as int != 0 {
            0int
        } else {
            cost[0]@[j - 1] as int
        }
    } else if houses[i] as int != 0 && houses[i] as int != j {
        1_000_001int
    } else {
        let paint_cost: int = if houses[i] as int != 0 {
            0int
        } else {
            cost[i]@[j - 1] as int
        };
        let same = dp_spec(houses, cost, n, i - 1, j, k);
        let diff = min_excluding(houses, cost, n, i - 1, j, k - 1, 1);
        let best = spec_min(same, diff);
        if best >= 1_000_001int || paint_cost + best >= 1_000_001int {
            1_000_001int
        } else {
            paint_cost + best
        }
    }
}


pub open spec fn min_excluding(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    n: int,
    i: int,
    exclude: int,
    k: int,
    from_c: int,
) -> int
    decreases i, n - from_c + 1,
{
    if from_c > n {
        1_000_001int
    } else if from_c == exclude {
        min_excluding(houses, cost, n, i, exclude, k, from_c + 1)
    } else {
        spec_min(
            dp_spec(houses, cost, n, i, from_c, k),
            min_excluding(houses, cost, n, i, exclude, k, from_c + 1),
        )
    }
}


pub open spec fn min_final(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    n: int,
    m: int,
    target: int,
    from_c: int,
) -> int
    decreases n - from_c + 1,
{
    if from_c > n {
        1_000_001int
    } else {
        spec_min(
            dp_spec(houses, cost, n, m - 1, from_c, target),
            min_final(houses, cost, n, m, target, from_c + 1),
        )
    }
}



pub open spec fn answer_spec(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    n: int,
    m: int,
    target: int,
) -> int {
    let min_val = min_final(houses, cost, n, m, target, 1);
    if min_val >= 1_000_001int {
        -1int
    } else {
        min_val
    }
}

pub open spec fn dp_idx(j: int, k: int, stride: int) -> int {
    j * stride + k
}

proof fn lemma_dp_spec_base(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    n: int,
    jj: int,
    kk: int,
)
    requires
        houses.len() >= 1,
        cost.len() >= 1,
        cost[0]@.len() == n,
        1 <= n,
    ensures
        (jj == 0 || kk == 0 || kk > 1 || jj < 1 || jj > n) ==> dp_spec(houses, cost, n, 0, jj,
            kk) == 1_000_001int,
        (1 <= jj <= n && kk == 1 && houses[0] as int != 0 && houses[0] as int == jj) ==> dp_spec(
            houses,
            cost,
            n,
            0,
            jj,
            kk,
        ) == 0int,
        (1 <= jj <= n && kk == 1 && houses[0] as int != 0 && houses[0] as int != jj) ==> dp_spec(
            houses,
            cost,
            n,
            0,
            jj,
            kk,
        ) == 1_000_001int,
        (1 <= jj <= n && kk == 1 && houses[0] as int == 0) ==> dp_spec(houses, cost, n, 0, jj,
            kk) == cost[0]@[jj - 1] as int,
{
}

proof fn lemma_spec_min_assoc(a: int, b: int, c: int)
    ensures
        spec_min(a, spec_min(b, c)) == spec_min(spec_min(a, b), c),
{
}

proof fn lemma_dp_idx_disjoint_j(j1: int, k1: int, j2: int, k2: int, stride: int)
    requires
        stride > 0,
        0 <= k1 < stride,
        0 <= k2 < stride,
        j1 >= 0,
        j2 >= 0,
        j1 != j2,
    ensures
        j1 * stride + k1 != j2 * stride + k2,
{
    assert(j1 * stride + k1 != j2 * stride + k2) by (nonlinear_arith)
        requires stride > 0, 0 <= k1 < stride, 0 <= k2 < stride, j1 >= 0, j2 >= 0, j1 != j2;
}

proof fn lemma_dp_spec_bound(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    n: int,
    m: int,
    i: int,
    j: int,
    k: int,
)
    requires
        1 <= m,
        1 <= n,
        i < m,
        cost.len() >= m,
        houses.len() >= m,
        forall|ii: int| 0 <= ii < m ==> (#[trigger] cost[ii])@.len() == n,
        forall|ii: int, jj: int| 0 <= ii < m && 0 <= jj < n ==> 1 <= #[trigger] cost[ii]@[jj] <= 10_000,
    ensures
        dp_spec(houses, cost, n, i, j, k) <= 1_000_001,
    decreases i, 0int,
{
    if j < 1 || j > n || k < 1 || k > i + 1 {
    } else if i == 0 {
        if k != 1 {
        } else if houses[0] as int != 0 && houses[0] as int != j {
        } else if houses[0] as int != 0 {
        } else {
            assert(cost[0]@[j - 1] as int <= 10_000);
        }
    } else if houses[i] as int != 0 && houses[i] as int != j {
    } else {
        lemma_dp_spec_bound(houses, cost, n, m, i - 1, j, k);
        lemma_min_excluding_bound(houses, cost, n, m, i - 1, j, k - 1, 1);
    }
}

proof fn lemma_min_excluding_bound(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    n: int,
    m: int,
    i: int,
    exclude: int,
    k: int,
    from_c: int,
)
    requires
        1 <= m,
        1 <= n,
        i < m,
        cost.len() >= m,
        houses.len() >= m,
        forall|ii: int| 0 <= ii < m ==> (#[trigger] cost[ii])@.len() == n,
        forall|ii: int, jj: int| 0 <= ii < m && 0 <= jj < n ==> 1 <= #[trigger] cost[ii]@[jj] <= 10_000,
    ensures
        min_excluding(houses, cost, n, i, exclude, k, from_c) <= 1_000_001,
    decreases i, n - from_c + 1,
{
    if from_c > n {
    } else if from_c == exclude {
        lemma_min_excluding_bound(houses, cost, n, m, i, exclude, k, from_c + 1);
    } else {
        lemma_dp_spec_bound(houses, cost, n, m, i, from_c, k);
        lemma_min_excluding_bound(houses, cost, n, m, i, exclude, k, from_c + 1);
    }
}

proof fn lemma_min_excluding_all_large(
    houses: Seq<i32>,
    cost: Seq<Vec<i32>>,
    n: int,
    i: int,
    exclude: int,
    k: int,
    from_c: int,
)
    requires
        forall|c: int| from_c <= c <= n && c != exclude ==> dp_spec(houses, cost, n, i, c, k) >= 1_000_001int,
    ensures
        min_excluding(houses, cost, n, i, exclude, k, from_c) >= 1_000_001int,
    decreases n - from_c + 1,
{
    if from_c > n {
    } else if from_c == exclude {
        lemma_min_excluding_all_large(houses, cost, n, i, exclude, k, from_c + 1);
    } else {
        assert(dp_spec(houses, cost, n, i, from_c, k) >= 1_000_001int);
        lemma_min_excluding_all_large(houses, cost, n, i, exclude, k, from_c + 1);
    }
}

impl Solution {
    pub fn min_cost(
        houses: Vec<i32>,
        cost: Vec<Vec<i32>>,
        m: i32,
        n: i32,
        target: i32,
    ) -> (result: i32)
        requires
            m as int == houses@.len(),
            m as int == cost@.len(),
            1 <= m <= 100,
            1 <= n <= 20,
            1 <= target <= m,
            forall|i: int| 0 <= i < m as int ==> 0 <= #[trigger] houses@[i] <= n,
            forall|i: int|
                0 <= i < m as int ==> (#[trigger] cost@[i])@.len() == n as int,
            forall|i: int, j: int|
                0 <= i < m as int && 0 <= j < n as int ==> 1 <= #[trigger] cost@[i]@[j]
                    <= 10_000,
        ensures
            result as int == answer_spec(houses@, cost@, n as int, m as int, target as int),
    {
        let m_us = m as usize;
        let n_us = n as usize;
        let target_us = target as usize;
        let stride: usize = target_us + 1;

        assert((n_us as int + 1) * (stride as int) <= 21 * 101) by (nonlinear_arith)
            requires
                1 <= n <= 20,
                1 <= target <= m,
                1 <= m <= 100,
                stride == target_us + 1,
                n_us == n as usize,
                target_us == target as usize,
        ;

        let dp_size: usize = (n_us + 1) * stride;

        assert(dp_size <= 21 * 101) by (nonlinear_arith)
            requires
                1 <= n <= 20,
                1 <= target <= m,
                1 <= m <= 100,
                stride == target_us + 1,
                dp_size == (n_us + 1) * stride,
                n_us == n as usize,
                target_us == target as usize,
        ;

        let mut prev_dp: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < dp_size
            invariant
                idx <= dp_size,
                prev_dp@.len() == idx as int,
                dp_size == (n_us + 1) * stride,
                dp_size <= 21 * 101,
                forall|ii: int| 0 <= ii < idx as int ==> prev_dp@[ii] == 1_000_001i32,
            decreases dp_size - idx,
        {
            prev_dp.push(1_000_001i32);
            idx += 1;
        }

        assert(prev_dp@.len() == (dp_size as int));

        proof {
            assert forall|jj: int, kk: int|
                1 <= jj <= n as int && 0 <= kk <= target as int
                implies prev_dp@[dp_idx(jj, kk, stride as int)] == 1_000_001i32
            by {
                assert(dp_idx(jj, kk, stride as int) >= 0) by (nonlinear_arith)
                    requires 1 <= jj, 0 <= kk, stride as int >= 0;
                assert(dp_idx(jj, kk, stride as int) < dp_size as int) by (nonlinear_arith)
                    requires
                        1 <= jj <= n as int,
                        0 <= kk <= target as int,
                        stride as int == target as int + 1,
                        dp_size as int == (n as int + 1) * stride as int,
                        1 <= n <= 20,
                        1 <= target <= m,
                        1 <= m <= 100,
                ;
            }
            assert forall|kk: int|
                0 <= kk <= target as int
                implies prev_dp@[kk as int] == 1_000_001i32
            by {
                assert(0 <= kk);
                assert(kk < dp_size as int) by (nonlinear_arith)
                    requires
                        0 <= kk <= target as int,
                        stride as int == target as int + 1,
                        dp_size as int == (n as int + 1) * stride as int,
                        1 <= n <= 20,
                        1 <= target <= m,
                        1 <= m <= 100,
                ;
            }
        }

        let mut j: usize = 1;
        while j <= n_us
            invariant
                1 <= j <= n_us + 1,
                prev_dp@.len() == dp_size as int,
                m_us == m as usize,
                n_us == n as usize,
                target_us == target as usize,
                stride == target_us + 1,
                dp_size == (n_us + 1) * stride,
                dp_size <= 21 * 101,
                1 <= m <= 100,
                1 <= n <= 20,
                1 <= target <= m,
                m as int == houses@.len(),
                m as int == cost@.len(),
                forall|i: int| 0 <= i < m as int ==> 0 <= #[trigger] houses@[i] <= n,
                forall|i: int|
                    0 <= i < m as int ==> (#[trigger] cost@[i])@.len() == n as int,
                forall|i: int, jj: int|
                    0 <= i < m as int && 0 <= jj < n as int ==> 1
                        <= #[trigger] cost@[i]@[jj] <= 10_000,
                forall|jj: int, kk: int|
                    1 <= jj < j as int && 0 <= kk <= target as int ==> prev_dp@[dp_idx(
                        jj,
                        kk,
                        stride as int,
                    )] as int == dp_spec(houses@, cost@, n as int, 0, jj, kk),
                forall|jj: int, kk: int|
                    j as int <= jj <= n as int && 0 <= kk <= target as int
                        ==> prev_dp@[dp_idx(jj, kk, stride as int)] == 1_000_001i32,
                forall|kk: int|
                    0 <= kk <= target as int ==> prev_dp@[kk as int] == 1_000_001i32,
                forall|ii: int|
                    0 <= ii < dp_size as int ==> 0 <= #[trigger] prev_dp@[ii] <= 1_000_001,
            decreases n_us + 1 - j,
        {
            assert((j as int) * (stride as int) + (target as int) < (dp_size as int))
                by (nonlinear_arith)
                requires
                    1 <= j as int <= n as int,
                    1 <= n <= 20,
                    1 <= target <= m,
                    1 <= m <= 100,
                    stride == target_us + 1,
                    target_us == target as usize,
                    dp_size == (n_us + 1) * stride,
                    n_us == n as usize,
            ;
            if houses[0] != 0 {
                if houses[0] as usize == j {
                    prev_dp.set(j * stride + 1, 0i32);
                    proof {
                        lemma_dp_spec_base(houses@, cost@, n as int, j as int, 1);
                        assert(dp_spec(houses@, cost@, n as int, 0, j as int, 1) == 0int);
                        assert forall|kk: int|
                            0 <= kk <= target as int implies prev_dp@[dp_idx(
                            j as int,
                            kk,
                            stride as int,
                        )] as int == dp_spec(
                            houses@,
                            cost@,
                            n as int,
                            0,
                            j as int,
                            kk,
                        ) by {
                            if kk == 1 {
                            } else {
                                lemma_dp_spec_base(
                                    houses@,
                                    cost@,
                                    n as int,
                                    j as int,
                                    kk,
                                );
                            }
                        }
                        assert forall|jj: int, kk: int|
                            1 <= jj < j as int && 0 <= kk <= target as int
                            implies prev_dp@[dp_idx(jj, kk, stride as int)] as int == dp_spec(houses@, cost@, n as int, 0, jj, kk)
                        by {
                            assert(jj * (stride as int) <= (j as int - 1) * (stride as int)) by (nonlinear_arith)
                                requires jj <= j as int - 1, jj >= 1, stride as int >= 2;
                            assert((j as int - 1) * (stride as int) + target as int == (j as int) * (stride as int) - 1) by (nonlinear_arith)
                                requires stride as int == target as int + 1;
                            assert(jj * (stride as int) + kk <= (j as int) * (stride as int) - 1);
                        }
                        assert forall|jj: int, kk: int|
                            j as int + 1 <= jj && jj <= n as int && 0 <= kk <= target as int
                            implies prev_dp@[dp_idx(jj, kk, stride as int)] == 1_000_001i32
                        by {
                            assert(dp_idx(jj, kk, stride as int) == jj * (stride as int) + kk);
                            assert(jj * (stride as int) >= (j as int + 1) * (stride as int)) by (nonlinear_arith)
                                requires jj >= j as int + 1, stride as int >= 2;
                            assert((j as int + 1) * (stride as int) >= (j as int) * (stride as int) + 2) by (nonlinear_arith)
                                requires stride as int >= 2;
                            assert(jj * (stride as int) + kk >= (j as int) * (stride as int) + 2);
                            assert(dp_idx(jj, kk, stride as int) != (j as int) * (stride as int) + 1);
                            assert(0 <= dp_idx(jj, kk, stride as int)) by (nonlinear_arith)
                                requires 0 <= jj, 0 <= kk, stride as int >= 0;
                            assert(dp_idx(jj, kk, stride as int) < dp_size as int) by (nonlinear_arith)
                                requires 1 <= jj, jj <= n as int, 0 <= kk, kk <= target as int,
                                    stride as int == target as int + 1, dp_size as int == (n as int + 1) * (stride as int);
                        }
                        assert forall|kk: int|
                            0 <= kk <= target as int
                            implies prev_dp@[kk] == 1_000_001i32
                        by {
                            assert(kk != (j as int) * (stride as int) + 1) by (nonlinear_arith)
                                requires 0 <= kk <= target as int, stride as int == target as int + 1, 1 <= j as int;
                        }
                    }
                } else {
                    proof {
                        assert forall|kk: int|
                            0 <= kk <= target as int implies prev_dp@[dp_idx(
                            j as int,
                            kk,
                            stride as int,
                        )] as int == dp_spec(
                            houses@,
                            cost@,
                            n as int,
                            0,
                            j as int,
                            kk,
                        ) by {
                            lemma_dp_spec_base(houses@, cost@, n as int, j as int, kk);
                        }
                    }
                }
            } else {
                prev_dp.set(j * stride + 1, cost[0][j - 1]);
                proof {
                    lemma_dp_spec_base(houses@, cost@, n as int, j as int, 1);
                    assert(dp_spec(houses@, cost@, (n as int), 0, (j as int), 1) == (cost@[0]@[(j as int) - 1] as int));
                    assert forall|kk: int|
                        0 <= kk <= target as int implies prev_dp@[dp_idx(
                        j as int,
                        kk,
                        stride as int,
                    )] as int == dp_spec(
                        houses@,
                        cost@,
                        n as int,
                        0,
                        j as int,
                        kk,
                    ) by {
                        if kk == 1 {
                        } else {
                            lemma_dp_spec_base(houses@, cost@, n as int, j as int, kk);
                        }
                    }
                    assert forall|jj: int, kk: int|
                        1 <= jj < j as int && 0 <= kk <= target as int
                        implies prev_dp@[dp_idx(jj, kk, stride as int)] as int == dp_spec(houses@, cost@, n as int, 0, jj, kk)
                    by {
                        assert(jj * (stride as int) <= (j as int - 1) * (stride as int)) by (nonlinear_arith)
                            requires jj <= j as int - 1, jj >= 1, stride as int >= 2;
                        assert((j as int - 1) * (stride as int) + target as int == (j as int) * (stride as int) - 1) by (nonlinear_arith)
                            requires stride as int == target as int + 1;
                        assert(jj * (stride as int) + kk <= (j as int) * (stride as int) - 1);
                    }
                    assert forall|jj: int, kk: int|
                        j as int + 1 <= jj && jj <= n as int && 0 <= kk <= target as int
                        implies prev_dp@[dp_idx(jj, kk, stride as int)] == 1_000_001i32
                    by {
                        assert(dp_idx(jj, kk, stride as int) == jj * (stride as int) + kk);
                        assert(jj * (stride as int) >= (j as int + 1) * (stride as int)) by (nonlinear_arith)
                            requires jj >= j as int + 1, stride as int >= 2;
                        assert((j as int + 1) * (stride as int) >= (j as int) * (stride as int) + 2) by (nonlinear_arith)
                            requires stride as int >= 2;
                        assert(jj * (stride as int) + kk >= (j as int) * (stride as int) + 2);
                        assert(dp_idx(jj, kk, stride as int) != (j as int) * (stride as int) + 1);
                        assert(0 <= dp_idx(jj, kk, stride as int)) by (nonlinear_arith)
                            requires 0 <= jj, 0 <= kk, stride as int >= 0;
                        assert(dp_idx(jj, kk, stride as int) < dp_size as int) by (nonlinear_arith)
                            requires 1 <= jj, jj <= n as int, 0 <= kk, kk <= target as int,
                                stride as int == target as int + 1, dp_size as int == (n as int + 1) * (stride as int);
                    }
                    assert forall|kk: int|
                        0 <= kk <= target as int
                        implies prev_dp@[kk] == 1_000_001i32
                    by {
                        assert(kk != (j as int) * (stride as int) + 1) by (nonlinear_arith)
                            requires 0 <= kk <= target as int, stride as int == target as int + 1, 1 <= j as int;
                    }
                }
            }
            j += 1;
        }

        proof {
            assert forall|jj: int, kk: int|
                0 <= jj <= n as int && 0 <= kk <= target as int implies prev_dp@[dp_idx(
                jj,
                kk,
                stride as int,
            )] as int == dp_spec(houses@, cost@, n as int, 0, jj, kk) by {
                if jj == 0 {
                    lemma_dp_spec_base(houses@, cost@, n as int, 0, kk);
                }
            }
        }

        let ghost mut house_idx: int = 0;

        let mut i: usize = 1;
        while i < m_us
            invariant
                1 <= i <= m_us,
                house_idx == i as int - 1,
                prev_dp@.len() == dp_size as int,
                m_us == m as usize,
                n_us == n as usize,
                target_us == target as usize,
                stride == target_us + 1,
                dp_size == (n_us + 1) * stride,
                dp_size <= 21 * 101,
                1 <= m <= 100,
                1 <= n <= 20,
                1 <= target <= m,
                m as int == houses@.len(),
                m as int == cost@.len(),
                forall|i: int| 0 <= i < m as int ==> 0 <= #[trigger] houses@[i] <= n,
                forall|i: int|
                    0 <= i < m as int ==> (#[trigger] cost@[i])@.len() == n as int,
                forall|i: int, jj: int|
                    0 <= i < m as int && 0 <= jj < n as int ==> 1
                        <= #[trigger] cost@[i]@[jj] <= 10_000,
                forall|jj: int, kk: int|
                    0 <= jj <= n as int && 0 <= kk <= target as int ==> prev_dp@[dp_idx(
                        jj,
                        kk,
                        stride as int,
                    )] as int == dp_spec(
                        houses@,
                        cost@,
                        n as int,
                        house_idx,
                        jj,
                        kk,
                    ),
                forall|ii: int|
                    0 <= ii < dp_size as int ==> 0 <= #[trigger] prev_dp@[ii] <= 1_000_001,
            decreases m_us - i,
        {
            let mut curr_dp: Vec<i32> = Vec::new();
            let mut idx: usize = 0;
            while idx < dp_size
                invariant
                    idx <= dp_size,
                    curr_dp@.len() == idx as int,
                    dp_size == (n_us + 1) * stride,
                    dp_size <= 21 * 101,
                    forall|ii: int| 0 <= ii < idx as int ==> curr_dp@[ii] == 1_000_001i32,
                decreases dp_size - idx,
            {
                curr_dp.push(1_000_001i32);
                idx += 1;
            }

            proof {
                assert forall|jj: int, kk: int|
                    1 <= jj <= n as int && 0 <= kk <= target as int
                    implies curr_dp@[dp_idx(jj, kk, stride as int)] == 1_000_001i32
                by {
                    assert(dp_idx(jj, kk, stride as int) >= 0) by (nonlinear_arith)
                        requires 1 <= jj, 0 <= kk, stride as int >= 0;
                    assert(dp_idx(jj, kk, stride as int) < dp_size as int) by (nonlinear_arith)
                        requires
                            1 <= jj <= n as int,
                            0 <= kk <= target as int,
                            stride as int == target as int + 1,
                            dp_size as int == (n as int + 1) * stride as int,
                            1 <= n <= 20,
                            1 <= target <= m,
                            1 <= m <= 100,
                    ;
                }
                assert forall|kk: int|
                    0 <= kk <= target as int
                    implies curr_dp@[kk as int] == 1_000_001i32
                by {
                    assert(0 <= kk);
                    assert(kk < dp_size as int) by (nonlinear_arith)
                        requires
                            0 <= kk <= target as int,
                            stride as int == target as int + 1,
                            dp_size as int == (n as int + 1) * stride as int,
                            1 <= n <= 20,
                            1 <= target <= m,
                            1 <= m <= 100,
                    ;
                }
            }

            let mut j: usize = 1;
            while j <= n_us
                invariant
                    1 <= j <= n_us + 1,
                    curr_dp@.len() == dp_size as int,
                    prev_dp@.len() == dp_size as int,
                    m_us == m as usize,
                    n_us == n as usize,
                    target_us == target as usize,
                    stride == target_us + 1,
                    dp_size == (n_us + 1) * stride,
                    dp_size <= 21 * 101,
                    1 <= m <= 100,
                    1 <= n <= 20,
                    1 <= target <= m,
                    1 <= i < m_us,
                    house_idx == i as int - 1,
                    m as int == houses@.len(),
                    m as int == cost@.len(),
                    forall|i: int| 0 <= i < m as int ==> 0 <= #[trigger] houses@[i] <= n,
                    forall|i: int|
                        0 <= i < m as int ==> (#[trigger] cost@[i])@.len() == n as int,
                    forall|i: int, jj: int|
                        0 <= i < m as int && 0 <= jj < n as int ==> 1
                            <= #[trigger] cost@[i]@[jj] <= 10_000,
                    forall|jj: int, kk: int|
                        0 <= jj <= n as int && 0 <= kk <= target as int
                            ==> prev_dp@[dp_idx(jj, kk, stride as int)] as int == dp_spec(
                            houses@,
                            cost@,
                            n as int,
                            house_idx,
                            jj,
                            kk,
                        ),
                    forall|ii: int|
                        0 <= ii < dp_size as int ==> 0 <= #[trigger] prev_dp@[ii] <= 1_000_001,
                    forall|jj: int, kk: int|
                        1 <= jj < j as int && 0 <= kk <= target as int
                            ==> curr_dp@[dp_idx(jj, kk, stride as int)] as int == dp_spec(
                            houses@,
                            cost@,
                            n as int,
                            i as int,
                            jj,
                            kk,
                        ),
                    forall|jj: int, kk: int|
                        j as int <= jj <= n as int && 0 <= kk <= target as int
                            ==> curr_dp@[dp_idx(jj, kk, stride as int)] == 1_000_001i32,
                    forall|kk: int|
                        0 <= kk <= target as int ==> curr_dp@[kk as int] == 1_000_001i32,
                    forall|ii: int|
                        0 <= ii < dp_size as int ==> 0 <= #[trigger] curr_dp@[ii] <= 1_000_001,
                decreases n_us + 1 - j,
            {
                assert((j as int) * (stride as int) + (target as int) < (dp_size as int))
                    by (nonlinear_arith)
                    requires
                        1 <= j as int <= n as int,
                        1 <= n <= 20,
                        1 <= target <= m,
                        1 <= m <= 100,
                        stride == target_us + 1,
                        target_us == target as usize,
                        dp_size == (n_us + 1) * stride,
                        n_us == n as usize,
                ;

                if houses[i] == 0 || houses[i] as usize == j {
                    let paint_cost: i32 =
                        if houses[i] != 0 { 0i32 } else { cost[i][j - 1] };

                    proof {
                        assert(0 <= paint_cost <= 10_000) by {
                            if houses@[i as int] as int != 0 {
                            } else {
                                assert(cost@[i as int]@[j as int - 1] == paint_cost);
                            }
                        }
                    }

                    let mut k: usize = 1;
                    while k <= target_us
                        invariant
                            1 <= k <= target_us + 1,
                            curr_dp@.len() == dp_size as int,
                            prev_dp@.len() == dp_size as int,
                            m_us == m as usize,
                            n_us == n as usize,
                            target_us == target as usize,
                            stride == target_us + 1,
                            dp_size == (n_us + 1) * stride,
                            dp_size <= 21 * 101,
                            1 <= m <= 100,
                            1 <= n <= 20,
                            1 <= target <= m,
                            1 <= i < m_us,
                            1 <= j as int <= n as int,
                            house_idx == i as int - 1,
                            0 <= paint_cost <= 10_000,
                            m as int == houses@.len(),
                            m as int == cost@.len(),
                            houses@[i as int] == 0 || houses@[i as int] as int == j as int,
                            forall|i: int|
                                0 <= i < m as int ==> 0 <= #[trigger] houses@[i] <= n,
                            forall|i: int|
                                0 <= i < m as int ==> (#[trigger] cost@[i])@.len()
                                    == n as int,
                            forall|i: int, jj: int|
                                0 <= i < m as int && 0 <= jj < n as int ==> 1
                                    <= #[trigger] cost@[i]@[jj] <= 10_000,
                            forall|jj: int, kk: int|
                                0 <= jj <= n as int && 0 <= kk <= target as int
                                    ==> prev_dp@[dp_idx(jj, kk, stride as int)] as int
                                    == dp_spec(
                                    houses@,
                                    cost@,
                                    n as int,
                                    house_idx,
                                    jj,
                                    kk,
                                ),
                            forall|ii: int|
                                0 <= ii < dp_size as int ==> 0 <= #[trigger] prev_dp@[ii] <= 1_000_001,
                            paint_cost as int == (if houses@[i as int] as int != 0 {
                                0int
                            } else {
                                cost@[i as int]@[j as int - 1] as int
                            }),
                            forall|kk: int|
                                1 <= kk < k as int ==> curr_dp@[dp_idx(
                                    j as int,
                                    kk,
                                    stride as int,
                                )] as int == dp_spec(
                                    houses@,
                                    cost@,
                                    n as int,
                                    i as int,
                                    j as int,
                                    kk,
                                ),
                            forall|kk: int|
                                k as int <= kk <= target as int ==> curr_dp@[dp_idx(
                                    j as int,
                                    kk,
                                    stride as int,
                                )] == 1_000_001i32,
                            curr_dp@[dp_idx(j as int, 0, stride as int)]
                                == 1_000_001i32,
                            forall|jj: int, kk: int|
                                1 <= jj < j as int && 0 <= kk <= target as int
                                    ==> curr_dp@[dp_idx(jj, kk, stride as int)] as int
                                    == dp_spec(
                                    houses@,
                                    cost@,
                                    n as int,
                                    i as int,
                                    jj,
                                    kk,
                                ),
                            forall|jj: int, kk: int|
                                (j as int) < jj <= n as int && 0 <= kk <= target as int
                                    ==> curr_dp@[dp_idx(jj, kk, stride as int)]
                                    == 1_000_001i32,
                            forall|kk: int|
                                0 <= kk <= target as int ==> curr_dp@[kk as int]
                                    == 1_000_001i32,
                            forall|ii: int|
                                0 <= ii < dp_size as int ==> 0 <= #[trigger] curr_dp@[ii]
                                    <= 1_000_001,
                        decreases target_us + 1 - k,
                    {
                        assert((j as int) * (stride as int) + (k as int) < (dp_size as int))
                            by (nonlinear_arith)
                            requires
                                1 <= j as int <= n as int,
                                1 <= k as int <= target as int,
                                1 <= n <= 20,
                                1 <= target <= m,
                                1 <= m <= 100,
                                stride == target_us + 1,
                                target_us == target as usize,
                                dp_size == (n_us + 1) * stride,
                                n_us == n as usize,
                        ;

                        let same: i32 = prev_dp[j * stride + k];

                        let mut diff: i32 = 1_000_001i32;
                        let mut c: usize = 1;
                        proof {
                            lemma_min_excluding_bound(houses@, cost@, n as int, m as int, house_idx, j as int, k as int - 1, 1);
                        }
                        while c <= n_us
                            invariant
                                1 <= c <= n_us + 1,
                                prev_dp@.len() == dp_size as int,
                                m_us == m as usize,
                                n_us == n as usize,
                                target_us == target as usize,
                                stride == target_us + 1,
                                dp_size == (n_us + 1) * stride,
                                dp_size <= 21 * 101,
                                1 <= m <= 100,
                                1 <= n <= 20,
                                1 <= target <= m,
                                1 <= i < m_us,
                                1 <= j as int <= n as int,
                                1 <= k as int <= target as int,
                                house_idx == i as int - 1,
                                forall|jj: int, kk: int|
                                    0 <= jj <= n as int && 0 <= kk <= target as int
                                        ==> prev_dp@[dp_idx(jj, kk, stride as int)]
                                        as int == dp_spec(
                                        houses@,
                                        cost@,
                                        n as int,
                                        house_idx,
                                        jj,
                                        kk,
                                    ),
                                forall|ii: int|
                                    0 <= ii < dp_size as int ==> 0 <= #[trigger] prev_dp@[ii]
                                        <= 1_000_001,
                                0 <= diff <= 1_000_001,
                                spec_min(
                                    diff as int,
                                    min_excluding(
                                        houses@,
                                        cost@,
                                        n as int,
                                        house_idx,
                                        j as int,
                                        k as int - 1,
                                        c as int,
                                    ),
                                ) == min_excluding(
                                    houses@,
                                    cost@,
                                    n as int,
                                    house_idx,
                                    j as int,
                                    k as int - 1,
                                    1,
                                ),
                            decreases n_us + 1 - c,
                        {
                            assert(c as int * stride as int + (k as int - 1) < dp_size
                                as int) by (nonlinear_arith)
                                requires
                                    1 <= c as int <= n as int,
                                    1 <= k as int <= target as int,
                                    1 <= n <= 20,
                                    1 <= target <= m,
                                    1 <= m <= 100,
                                    stride == target_us + 1,
                                    target_us == target as usize,
                                    dp_size == (n_us + 1) * stride,
                                    n_us == n as usize,
                            ;

                            if c != j {
                                let val: i32 = prev_dp[c * stride + (k - 1)];
                                proof {
                                    assert(val as int == dp_spec(
                                        houses@,
                                        cost@,
                                        n as int,
                                        house_idx,
                                        c as int,
                                        k as int - 1,
                                    ));
                                    let me_old = min_excluding(
                                        houses@,
                                        cost@,
                                        n as int,
                                        house_idx,
                                        j as int,
                                        k as int - 1,
                                        c as int,
                                    );
                                    let me_rest = min_excluding(
                                        houses@,
                                        cost@,
                                        n as int,
                                        house_idx,
                                        j as int,
                                        k as int - 1,
                                        c as int + 1,
                                    );
                                    assert(me_old == spec_min(val as int, me_rest));
                                }
                                if val < diff {
                                    proof {
                                        let me_rest = min_excluding(
                                            houses@,
                                            cost@,
                                            n as int,
                                            house_idx,
                                            j as int,
                                            k as int - 1,
                                            c as int + 1,
                                        );
                                        lemma_spec_min_assoc(
                                            diff as int,
                                            val as int,
                                            me_rest,
                                        );
                                        assert(spec_min(diff as int, spec_min(
                                            val as int,
                                            me_rest,
                                        )) == spec_min(
                                            spec_min(diff as int, val as int),
                                            me_rest,
                                        ));
                                        assert(spec_min((diff as int), (val as int))
                                            == (val as int));
                                    }
                                    diff = val;
                                } else {
                                    proof {
                                        let me_rest = min_excluding(
                                            houses@,
                                            cost@,
                                            n as int,
                                            house_idx,
                                            j as int,
                                            k as int - 1,
                                            c as int + 1,
                                        );
                                        lemma_spec_min_assoc(
                                            diff as int,
                                            val as int,
                                            me_rest,
                                        );
                                        assert(spec_min((diff as int), (val as int))
                                            == (diff as int));
                                    }
                                }
                            } else {
                                proof {
                                    assert(min_excluding(
                                        houses@,
                                        cost@,
                                        n as int,
                                        house_idx,
                                        j as int,
                                        k as int - 1,
                                        c as int,
                                    ) == min_excluding(
                                        houses@,
                                        cost@,
                                        n as int,
                                        house_idx,
                                        j as int,
                                        k as int - 1,
                                        c as int + 1,
                                    ));
                                }
                            }
                            c += 1;
                        }

                        proof {
                            assert(min_excluding(
                                houses@,
                                cost@,
                                n as int,
                                house_idx,
                                j as int,
                                k as int - 1,
                                n as int + 1,
                            ) == 1_000_001int);
                            assert(diff as int == min_excluding(
                                houses@,
                                cost@,
                                n as int,
                                house_idx,
                                j as int,
                                k as int - 1,
                                1,
                            ));
                        }

                        let best: i32 = if same <= diff { same } else { diff };

                        proof {
                            assert(same as int == dp_spec(
                                houses@,
                                cost@,
                                n as int,
                                house_idx,
                                j as int,
                                k as int,
                            ));
                            assert(diff as int == min_excluding(
                                houses@,
                                cost@,
                                n as int,
                                house_idx,
                                j as int,
                                k as int - 1,
                                1,
                            ));
                            assert((best as int) == spec_min((same as int), (diff as int)));
                        }

                        if best < 1_000_001i32 {
                            let total: i32 = paint_cost + best;
                            if total < 1_000_001i32 {
                                curr_dp.set(j * stride + k, total);
                                proof {
                                    assert((total as int) == (paint_cost as int) + (best as int));
                                    assert(house_idx == i as int - 1);
                                    let same_spec = dp_spec(houses@, cost@, n as int, i as int - 1, j as int, k as int);
                                    let diff_spec = min_excluding(houses@, cost@, n as int, i as int - 1, j as int, k as int - 1, 1);
                                    assert(same as int == same_spec);
                                    assert(diff as int == diff_spec);
                                    assert(best as int == spec_min(same_spec, diff_spec));
                                    assert(spec_min(same_spec, diff_spec) < 1_000_001int);
                                    assert(paint_cost as int + spec_min(same_spec, diff_spec) < 1_000_001int);
                                    
                                    assert(k as int <= i as int + 1) by {
                                        if k as int > i as int + 1 {
                                            
                                            assert(dp_spec(houses@, cost@, n as int, i as int - 1, j as int, k as int) == 1_000_001int);
                                            assert(same_spec == 1_000_001int);
                                            assert forall|c: int| 1 <= c <= n as int && c != j as int
                                                implies #[trigger] dp_spec(houses@, cost@, n as int, i as int - 1, c, k as int - 1) >= 1_000_001int
                                            by {
                                                assert(k as int - 1 > i as int) by (nonlinear_arith)
                                                    requires k as int > i as int + 1;
                                                assert(k as int - 1 > (i as int - 1) + 1) by (nonlinear_arith)
                                                    requires k as int - 1 > i as int;
                                            };
                                            lemma_min_excluding_all_large(houses@, cost@, n as int, i as int - 1, j as int, k as int - 1, 1);
                                            assert(diff_spec >= 1_000_001int);
                                            lemma_min_excluding_bound(houses@, cost@, n as int, m as int, i as int - 1, j as int, k as int - 1, 1);
                                            assert(diff_spec == 1_000_001int);
                                            assert(spec_min(same_spec, diff_spec) == 1_000_001int);
                                        }
                                    };
                                    let dp_val = dp_spec(
                                        houses@,
                                        cost@,
                                        n as int,
                                        i as int,
                                        j as int,
                                        k as int,
                                    );
                                    assert(dp_val == (total as int));
                                    
                                    assert forall|kk: int|
                                        k as int + 1 <= kk && kk <= target as int
                                        implies curr_dp@[dp_idx(j as int, kk, stride as int)] == 1_000_001i32
                                    by {
                                        assert(dp_idx(j as int, kk, stride as int) == (j as int) * (stride as int) + kk);
                                        assert(kk != k as int);
                                        assert((j as int) * (stride as int) + kk != (j as int) * (stride as int) + (k as int));
                                        assert(0 <= dp_idx(j as int, kk, stride as int)) by (nonlinear_arith)
                                            requires 0 <= j as int, 0 <= kk, stride as int >= 0;
                                        assert(dp_idx(j as int, kk, stride as int) < dp_size as int) by (nonlinear_arith)
                                            requires 1 <= j as int, j as int <= n as int, 0 <= kk, kk <= target as int,
                                                stride as int == target as int + 1, dp_size as int == (n as int + 1) * (stride as int);
                                    }
                                    
                                    assert forall|jj: int, kk: int|
                                        1 <= jj < j as int && 0 <= kk <= target as int
                                        implies curr_dp@[dp_idx(jj, kk, stride as int)] as int == dp_spec(houses@, cost@, n as int, i as int, jj, kk)
                                    by {
                                        assert(jj * (stride as int) <= (j as int - 1) * (stride as int)) by (nonlinear_arith)
                                            requires jj <= j as int - 1, jj >= 1, stride as int >= 2;
                                        assert((j as int - 1) * (stride as int) + target as int == (j as int) * (stride as int) - 1) by (nonlinear_arith)
                                            requires stride as int == target as int + 1;
                                        assert(jj * (stride as int) + kk <= (j as int) * (stride as int) - 1);
                                        assert((j as int) * (stride as int) + (k as int) >= (j as int) * (stride as int) + 1);
                                    }
                                    
                                    assert forall|jj: int, kk: int|
                                        (j as int) < jj <= n as int && 0 <= kk <= target as int
                                        implies curr_dp@[dp_idx(jj, kk, stride as int)] == 1_000_001i32
                                    by {
                                        assert(dp_idx(jj, kk, stride as int) == jj * (stride as int) + kk);
                                        assert(jj * (stride as int) + kk >= (j as int) * (stride as int) + stride as int) by (nonlinear_arith)
                                            requires jj >= j as int + 1, stride as int >= 2, kk >= 0;
                                        assert(stride as int == target as int + 1);
                                        assert(k as int <= target as int);
                                        assert((j as int) * (stride as int) + stride as int > (j as int) * (stride as int) + (k as int));
                                        assert(dp_idx(jj, kk, stride as int) > (j as int) * (stride as int) + (k as int));
                                        assert(dp_idx(jj, kk, stride as int) != (j as int) * (stride as int) + (k as int));
                                        assert(0 <= dp_idx(jj, kk, stride as int)) by (nonlinear_arith)
                                            requires 0 <= jj, 0 <= kk, stride as int >= 0;
                                        assert(dp_idx(jj, kk, stride as int) < dp_size as int) by (nonlinear_arith)
                                            requires 1 <= jj, jj <= n as int, 0 <= kk, kk <= target as int,
                                                stride as int == target as int + 1, dp_size as int == (n as int + 1) * (stride as int);
                                    }
                                    
                                    assert forall|kk: int|
                                        0 <= kk <= target as int
                                        implies curr_dp@[kk] == 1_000_001i32
                                    by {
                                        assert(0 <= kk);
                                        assert(kk < dp_size as int) by (nonlinear_arith)
                                            requires kk <= target as int, stride as int == target as int + 1,
                                                dp_size as int == (n as int + 1) * (stride as int), n as int >= 1;
                                        assert((j as int) * (stride as int) >= stride as int) by (nonlinear_arith)
                                            requires 1 <= j as int, stride as int >= 0;
                                        assert(stride as int == target as int + 1);
                                        assert(k as int >= 1);
                                        assert((j as int) * (stride as int) + (k as int) >= target as int + 2);
                                        assert(kk <= target as int);
                                        assert(kk != (j as int) * (stride as int) + (k as int));
                                    }
                                    
                                    assert(curr_dp@[dp_idx(j as int, 0, stride as int)] == 1_000_001i32) by {
                                        assert((j as int) * (stride as int) + 0 != (j as int) * (stride as int) + (k as int));
                                    }
                                }
                            } else {
                                proof {
                                    let dp_val = dp_spec(
                                        houses@,
                                        cost@,
                                        n as int,
                                        i as int,
                                        j as int,
                                        k as int,
                                    );
                                    assert(dp_val == 1_000_001int);
                                }
                            }
                        } else {
                            proof {
                                let dp_val = dp_spec(
                                    houses@,
                                    cost@,
                                    n as int,
                                    i as int,
                                    j as int,
                                    k as int,
                                );
                                assert(dp_val == 1_000_001int);
                            }
                        }

                        k += 1;
                    }

                } else {
                    proof {
                        assert forall|kk: int|
                            0 <= kk <= target as int implies curr_dp@[dp_idx(
                            j as int,
                            kk,
                            stride as int,
                        )] as int == dp_spec(
                            houses@,
                            cost@,
                            n as int,
                            i as int,
                            j as int,
                            kk,
                        ) by {
                            assert((houses@[(i as int)] as int) != 0);
                            assert((houses@[(i as int)] as int) != (j as int));
                            assert(dp_spec(
                                houses@,
                                cost@,
                                n as int,
                                i as int,
                                j as int,
                                kk,
                            ) == 1_000_001int);
                        }
                    }
                }
                j += 1;
            }

            proof {
                assert forall|jj: int, kk: int|
                    0 <= jj <= n as int && 0 <= kk <= target as int
                        implies curr_dp@[dp_idx(jj, kk, stride as int)] as int == dp_spec(
                    houses@,
                    cost@,
                    n as int,
                    i as int,
                    jj,
                    kk,
                ) by {
                    if jj == 0 {
                        assert(dp_idx(0, kk, stride as int) == kk);
                        assert(dp_spec(houses@, cost@, n as int, i as int, 0, kk)
                            == 1_000_001int);
                    }
                }
            }

            prev_dp = curr_dp;
            proof {
                house_idx = house_idx + 1;
            }
            i += 1;
        }

        proof {
            assert(house_idx == m as int - 1);
        }

        let mut ans: i32 = 1_000_001i32;
        let mut j: usize = 1;
        while j <= n_us
            invariant
                1 <= j <= n_us + 1,
                prev_dp@.len() == dp_size as int,
                m_us == m as usize,
                n_us == n as usize,
                target_us == target as usize,
                stride == target_us + 1,
                dp_size == (n_us + 1) * stride,
                dp_size <= 21 * 101,
                1 <= m <= 100,
                1 <= n <= 20,
                1 <= target <= m,
                house_idx == m as int - 1,
                forall|jj: int, kk: int|
                    0 <= jj <= n as int && 0 <= kk <= target as int ==> prev_dp@[dp_idx(
                        jj,
                        kk,
                        stride as int,
                    )] as int == dp_spec(
                        houses@,
                        cost@,
                        n as int,
                        house_idx,
                        jj,
                        kk,
                    ),
                0 <= ans <= 1_000_001,
                forall|ii: int|
                    0 <= ii < dp_size as int ==> 0 <= #[trigger] prev_dp@[ii] <= 1_000_001,
                ans as int == min_final(
                    houses@,
                    cost@,
                    n as int,
                    m as int,
                    target as int,
                    j as int,
                ) ==> ans as int == min_final(
                    houses@,
                    cost@,
                    n as int,
                    m as int,
                    target as int,
                    j as int,
                ),
                spec_min(
                    ans as int,
                    min_final(
                        houses@,
                        cost@,
                        n as int,
                        m as int,
                        target as int,
                        j as int,
                    ),
                ) == min_final(
                    houses@,
                    cost@,
                    n as int,
                    m as int,
                    target as int,
                    1,
                ),
            decreases n_us + 1 - j,
        {
            assert((j as int) * (stride as int) + (target as int) < (dp_size as int))
                by (nonlinear_arith)
                requires
                    1 <= j as int <= n as int,
                    1 <= n <= 20,
                    1 <= target <= m,
                    1 <= m <= 100,
                    stride == target_us + 1,
                    target_us == target as usize,
                    dp_size == (n_us + 1) * stride,
                    n_us == n as usize,
            ;

            let val: i32 = prev_dp[j * stride + target_us];

            proof {
                assert(val as int == dp_spec(
                    houses@,
                    cost@,
                    n as int,
                    m as int - 1,
                    j as int,
                    target as int,
                ));
                let mf_cur = min_final(
                    houses@,
                    cost@,
                    n as int,
                    m as int,
                    target as int,
                    j as int,
                );
                let mf_rest = min_final(
                    houses@,
                    cost@,
                    n as int,
                    m as int,
                    target as int,
                    j as int + 1,
                );
                assert(mf_cur == spec_min(val as int, mf_rest));
            }

            if val < ans {
                proof {
                    let mf_rest = min_final(
                        houses@,
                        cost@,
                        n as int,
                        m as int,
                        target as int,
                        j as int + 1,
                    );
                    lemma_spec_min_assoc(ans as int, val as int, mf_rest);
                    assert(spec_min((ans as int), (val as int)) == (val as int));
                }
                ans = val;
            } else {
                proof {
                    let mf_rest = min_final(
                        houses@,
                        cost@,
                        n as int,
                        m as int,
                        target as int,
                        j as int + 1,
                    );
                    lemma_spec_min_assoc(ans as int, val as int, mf_rest);
                    assert(spec_min((ans as int), (val as int)) == (ans as int));
                }
            }
            j += 1;
        }

        proof {
            assert(min_final(
                houses@,
                cost@,
                n as int,
                m as int,
                target as int,
                n as int + 1,
            ) == 1_000_001int);
            assert(ans as int == min_final(
                houses@,
                cost@,
                n as int,
                m as int,
                target as int,
                1,
            ));
            if ans >= 1_000_001i32 {
                assert(answer_spec(houses@, cost@, (n as int), (m as int), (target as int))
                    == -1int);
            } else {
                assert(answer_spec(houses@, cost@, (n as int), (m as int), (target as int))
                    == (ans as int));
            }
        }

        if ans >= 1_000_001i32 { -1i32 } else { ans }
    }
}

}
