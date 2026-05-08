use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ways_bounded(coins: Seq<i32>, amount: int, i: nat, j: int) -> bool {
        Self::coin_change_ways(coins, i, j) <= 1073741823
    }

    pub open spec fn coin_change_ways(coins: Seq<i32>, coins_used: nat, amount: int) -> int
        decreases coins_used, amount,
    {
        if coins_used == 0 {
            if amount == 0 {
                1
            } else {
                0
            }
        } else {
            let idx = (coins_used - 1) as int;
            let c = coins[idx] as int;
            Self::coin_change_ways(coins, (coins_used - 1) as nat, amount)
                + (if 1 <= c <= amount {
                    Self::coin_change_ways(coins, coins_used, amount - c)
                } else {
                    0
                })
        }
    }

    pub fn change(amount: i32, coins: Vec<i32>) -> (res: i32)
        requires
            0 <= amount <= 5000,
            1 <= coins.len() <= 300,
            forall |i: int| 0 <= i < coins.len() ==> 1 <= #[trigger] coins[i] <= 5000,
            forall |i: int, j: int| 0 <= i < j < coins.len() ==> coins[i] != coins[j],
            forall |i: nat, a: int|
                i <= (coins@).len() && 0 <= a <= amount as int
                    ==> #[trigger] Self::ways_bounded(coins@, amount as int, i, a),
        ensures
            res as int == Self::coin_change_ways(coins@, coins.len() as nat, amount as int),
    {
        let amount_usize = amount as usize;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= amount_usize {
            dp.push(0);
            k += 1;
        }
        dp.set(0, 1);
        let mut i: usize = 0;
        while i < coins.len() {
            let coin = coins[i] as usize;
            let mut j: usize = coin;
            while j <= amount_usize {
                let old_dp_j = dp[j];
                let add = dp[j - coin];
                dp.set(j, old_dp_j + add);
                j += 1;
            }
            i += 1;
        }
        dp[amount_usize]
    }
}

}
