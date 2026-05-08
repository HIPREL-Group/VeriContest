use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;
















impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }


    pub open spec fn min_col_cost(cost: Seq<Seq<i32>>, j: int, i: int) -> int
        decreases cost.len() - i,
    {
        if i >= cost.len() {
            101int
        } else {
            Self::min2(cost[i][j] as int, Self::min_col_cost(cost, j, i + 1))
        }
    }


    pub open spec fn unconnected_cost(cost: Seq<Seq<i32>>, n: int, mask: u32, j: int) -> int
        decreases n - j,
    {
        if j >= n {
            0int
        } else if (mask & (1u32 << (j as u32))) == 0u32 {
            Self::min_col_cost(cost, j, 0) + Self::unconnected_cost(cost, n, mask, j + 1)
        } else {
            Self::unconnected_cost(cost, n, mask, j + 1)
        }
    }




    pub open spec fn dp(cost: Seq<Seq<i32>>, m: int, n: int, row: int, mask: u32, j: int) -> int
        decreases m - row, n - j,
    {
        if row >= m {
            Self::unconnected_cost(cost, n, mask, 0)
        } else if j >= n {
            100_000int
        } else {
            let new_mask = (mask | (1u32 << (j as u32)));
            let connect_j = cost[row][j] as int + Self::dp(cost, m, n, row + 1, new_mask, 0);
            let skip_j = Self::dp(cost, m, n, row, mask, j + 1);
            Self::min2(connect_j, skip_j)
        }
    }

    pub fn connect_two_groups(cost: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= cost.len() <= 12,
            forall|i: int|
                0 <= i < cost.len() ==> (#[trigger] cost[i])@.len() == cost[0]@.len(),
            1 <= cost[0]@.len() <= 12,
            cost.len() >= cost[0]@.len(),
            forall|i: int, j: int|
                #![trigger cost[i]@[j]]
                0 <= i < cost.len() && 0 <= j < cost[0]@.len()
                    ==> 0 <= cost[i]@[j] <= 100,
        ensures
            result as int == Self::dp(
                Seq::new(cost.len() as nat, |i: int| cost[i]@),
                cost.len() as int,
                cost[0]@.len() as int,
                0,
                0u32,
                0,
            ),
    {
        let m = cost.len();
        let n = cost[0].len();
        let total_masks: usize = 1usize << n;


        let mut min_cost: Vec<i32> = Vec::new();
        let mut jj: usize = 0;
        while jj < n {
            let mut mc: i32 = cost[0][jj];
            let mut ii: usize = 1;
            while ii < m {
                if cost[ii][jj] < mc {
                    mc = cost[ii][jj];
                }
                ii = ii + 1;
            }
            min_cost.push(mc);
            jj = jj + 1;
        }

        let mut dp: Vec<i32> = Vec::new();
        let mut mask: usize = 0;
        while mask < total_masks {
            let mut uc: i32 = 0;
            let mut j: usize = 0;
            while j < n {
                if ((mask as u32) & (1u32 << (j as u32))) == 0u32 {
                    uc = uc + min_cost[j];
                }
                j = j + 1;
            }
            dp.push(uc);
            mask = mask + 1;
        }

        let mut row: usize = m;
        while row > 0 {
            row = row - 1;
            let mut new_dp: Vec<i32> = Vec::new();
            let mut mask: usize = 0;
            while mask < total_masks {
                let mut best: i32 = 100_000;
                let mut j: usize = 0;
                while j < n {
                    let new_mask: usize = mask | (1usize << j);
                    let val: i32 = cost[row][j] + dp[new_mask];
                    if val < best {
                        best = val;
                    }
                    j = j + 1;
                }
                new_dp.push(best);
                mask = mask + 1;
            }
            dp = new_dp;
        }

        dp[0]
    }
}

}
