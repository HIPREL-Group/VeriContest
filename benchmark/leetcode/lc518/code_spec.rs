use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn coin_change_ways(coins: Seq<i32>, coins_used: nat, amount: int) -> int
        decreases coins_used, amount,
    {
        if coins_used == 0 {
            if amount == 0 { 1 } else { 0 }
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

    pub open spec fn memo_sound(coins: Seq<i32>, memo: Seq<i32>, width: int) -> bool {
        forall |ii: int, aa: int| 0 <= ii <= coins.len() && 0 <= aa < width
            ==> #[trigger] memo[ii * width + aa] != -1
                ==> memo[ii * width + aa] as int == Self::coin_change_ways(coins, ii as nat, aa)
    }

    fn coin_rec(coins: &Vec<i32>, i: usize, a: usize, memo: &mut Vec<i32>, width: usize) -> (res: i32)
        requires
            forall |k: int| 0 <= k < coins.len() ==> 1 <= #[trigger] coins[k] <= 5000,
            coins.len() <= 300,
            width >= 1,
            old(memo).len() == (coins.len() + 1) * width,
            i <= coins.len(),
            a < width,
            Self::memo_sound(coins@, old(memo)@, width as int),
            Self::coin_change_ways(coins@, i as nat, a as int) <= i32::MAX,
        ensures
            res as int == Self::coin_change_ways(coins@, i as nat, a as int),
            memo.len() == old(memo).len(),
            Self::memo_sound(coins@, memo@, width as int),
    {
        let idx = i * width + a;
        let cur = memo[idx];
        if cur != -1 {
            return cur;
        }
        let result: i32;
        if i == 0 {
            result = if a == 0 { 1 } else { 0 };
        } else {
            let c = coins[i - 1];
            let part1 = Self::coin_rec(coins, i - 1, a, memo, width);
            let mut total = part1;
            if (c as usize) <= a {
                let part2 = Self::coin_rec(coins, i, a - c as usize, memo, width);
                total = total + part2;
            }
            result = total;
        }
        memo.set(idx, result);
        result
    }

    pub fn change(amount: i32, coins: Vec<i32>) -> (res: i32)
        requires
            0 <= amount <= 5000,
            1 <= coins.len() <= 300,
            forall |i: int| 0 <= i < coins.len() ==> 1 <= #[trigger] coins[i] <= 5000,
            forall |i: int, j: int| 0 <= i < j < coins.len() ==> coins[i] != coins[j],
            Self::coin_change_ways(coins@, coins.len() as nat, amount as int) <= i32::MAX,
        ensures
            res as int == Self::coin_change_ways(coins@, coins.len() as nat, amount as int),
    {
        let width = amount as usize + 1;
        let total_len = (coins.len() + 1) * width;
        let mut memo: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < total_len {
            memo.push(-1);
            k += 1;
        }
        Self::coin_rec(&coins, coins.len(), amount as usize, &mut memo, width)
    }
}

}
