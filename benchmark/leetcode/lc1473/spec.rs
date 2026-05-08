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
    }
}

}
