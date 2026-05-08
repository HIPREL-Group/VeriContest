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
        let dp_size: usize = (n_us + 1) * stride;

        let mut prev_dp: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < dp_size {
            prev_dp.push(1_000_001i32);
            idx += 1;
        }

        let mut j: usize = 1;
        while j <= n_us {
            if houses[0] != 0 {
                if houses[0] as usize == j {
                    prev_dp.set(j * stride + 1, 0i32);
                }
            } else {
                prev_dp.set(j * stride + 1, cost[0][j - 1]);
            }
            j += 1;
        }

        let mut i: usize = 1;
        while i < m_us {
            let mut curr_dp: Vec<i32> = Vec::new();
            let mut idx: usize = 0;
            while idx < dp_size {
                curr_dp.push(1_000_001i32);
                idx += 1;
            }

            let mut j: usize = 1;
            while j <= n_us {
                if houses[i] == 0 || houses[i] as usize == j {
                    let paint_cost: i32 =
                        if houses[i] != 0 { 0i32 } else { cost[i][j - 1] };

                    let mut k: usize = 1;
                    while k <= target_us {
                        let same: i32 = prev_dp[j * stride + k];

                        let mut diff: i32 = 1_000_001i32;
                        let mut c: usize = 1;
                        while c <= n_us {
                            if c != j {
                                let val: i32 = prev_dp[c * stride + (k - 1)];
                                if val < diff {
                                    diff = val;
                                }
                            }
                            c += 1;
                        }

                        let best: i32 = if same <= diff { same } else { diff };
                        if best < 1_000_001i32 {
                            let total: i32 = paint_cost + best;
                            if total < 1_000_001i32 {
                                curr_dp.set(j * stride + k, total);
                            }
                        }

                        k += 1;
                    }
                }
                j += 1;
            }

            prev_dp = curr_dp;
            i += 1;
        }

        let mut ans: i32 = 1_000_001i32;
        let mut j: usize = 1;
        while j <= n_us {
            let val: i32 = prev_dp[j * stride + target_us];
            if val < ans {
                ans = val;
            }
            j += 1;
        }

        if ans >= 1_000_001i32 { -1i32 } else { ans }
    }
}

}
