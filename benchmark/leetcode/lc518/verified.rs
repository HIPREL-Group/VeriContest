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

    proof fn lemma_ways_nonneg(coins: Seq<i32>, coins_used: nat, amount: int)
        requires
            coins_used <= coins.len(),
            0 <= amount,
        ensures
            0 <= Self::coin_change_ways(coins, coins_used, amount),
        decreases coins_used, amount,
    {
        if coins_used == 0 {
        } else if amount == 0 {
            Self::lemma_ways_nonneg(coins, (coins_used - 1) as nat, 0);
        } else {
            let c = coins[(coins_used - 1) as int] as int;
            if 1 <= c <= amount {
                Self::lemma_ways_nonneg(coins, coins_used, amount - c);
                Self::lemma_ways_nonneg(coins, (coins_used - 1) as nat, amount);
            } else {
                Self::lemma_ways_nonneg(coins, (coins_used - 1) as nat, amount);
            }
        }
    }

    proof fn lemma_bound_drop_index(coins: Seq<i32>, coins_used: nat, amount: int)
        requires
            coins_used > 0,
            coins_used <= coins.len(),
            0 <= amount,
        ensures
            Self::coin_change_ways(coins, (coins_used - 1) as nat, amount)
                <= Self::coin_change_ways(coins, coins_used, amount),
    {
        let c = coins[(coins_used - 1) as int] as int;
        if 1 <= c <= amount {
            Self::lemma_ways_nonneg(coins, coins_used, amount - c);
        }
    }

    proof fn lemma_bound_drop_amount(coins: Seq<i32>, coins_used: nat, amount: int)
        requires
            coins_used > 0,
            coins_used <= coins.len(),
            0 <= amount,
            1 <= coins[(coins_used - 1) as int] as int <= amount,
        ensures
            Self::coin_change_ways(coins, coins_used, amount - (coins[(coins_used - 1) as int] as int))
                <= Self::coin_change_ways(coins, coins_used, amount),
    {
        Self::lemma_ways_nonneg(coins, (coins_used - 1) as nat, amount);
    }

    pub open spec fn memo_sound(coins: Seq<i32>, memo: Seq<i32>, width: int) -> bool {
        forall |ii: int, aa: int| 0 <= ii <= coins.len() && 0 <= aa < width
            ==> #[trigger] memo[ii * width + aa] != -1
                ==> memo[ii * width + aa] as int == Self::coin_change_ways(coins, ii as nat, aa)
    }

    proof fn lemma_idx_bound(coins_len: int, width: int, ii: int, aa: int)
        requires
            0 <= ii <= coins_len,
            0 <= aa < width,
            width >= 1,
        ensures
            0 <= ii * width + aa < (coins_len + 1) * width,
    {
        assert(0 <= ii * width + aa < (coins_len + 1) * width) by (nonlinear_arith)
            requires
                0 <= ii <= coins_len,
                0 <= aa < width,
                width >= 1,
        {}
    }

    proof fn lemma_idx_unique(width: int, i1: int, a1: int, i2: int, a2: int)
        requires
            0 <= a1 < width,
            0 <= a2 < width,
            i1 * width + a1 == i2 * width + a2,
        ensures
            i1 == i2,
            a1 == a2,
    {
        assert((i1 - i2) * width == a2 - a1) by (nonlinear_arith)
            requires i1 * width + a1 == i2 * width + a2;
        if i1 != i2 {
            assert(i1 - i2 != 0);
            if i1 > i2 {
                assert((i1 - i2) * width >= width) by (nonlinear_arith)
                    requires i1 - i2 >= 1, width > 0;
                assert(false);
            } else {
                assert((i1 - i2) * width <= -width) by (nonlinear_arith)
                    requires i1 - i2 <= -1, width > 0;
                assert(false);
            }
        }
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
        decreases i, a,
    {
        proof {
            Self::lemma_idx_bound(coins.len() as int, width as int, i as int, a as int);
        }
        let idx = i * width + a;
        let cur = memo[idx];
        if cur != -1 {
            assert(Self::memo_sound(coins@, memo@, width as int));
            assert(memo@[idx as int] != -1);
            assert(memo@[idx as int] as int == Self::coin_change_ways(coins@, i as nat, a as int));
            return cur;
        }
        let result: i32;
        if i == 0 {
            result = if a == 0 { 1 } else { 0 };
        } else {
            let c = coins[i - 1];
            proof {
                Self::lemma_bound_drop_index(coins@, i as nat, a as int);
            }
            let part1 = Self::coin_rec(coins, i - 1, a, memo, width);
            let mut total = part1;
            if (c as usize) <= a {
                proof {
                    assert(1 <= c as int <= a as int);
                    Self::lemma_bound_drop_amount(coins@, i as nat, a as int);
                }
                let part2 = Self::coin_rec(coins, i, a - c as usize, memo, width);
                proof {
                    Self::lemma_ways_nonneg(coins@, (i - 1) as nat, a as int);
                    Self::lemma_ways_nonneg(coins@, i as nat, (a - c as usize) as int);
                    assert(Self::coin_change_ways(coins@, i as nat, a as int)
                        == Self::coin_change_ways(coins@, (i - 1) as nat, a as int)
                            + Self::coin_change_ways(coins@, i as nat, (a - c as usize) as int));
                }
                total = total + part2;
            } else {
                proof {
                    assert(!(1 <= c as int <= a as int));
                    assert(Self::coin_change_ways(coins@, i as nat, a as int)
                        == Self::coin_change_ways(coins@, (i - 1) as nat, a as int));
                }
            }
            result = total;
        }
        proof {
            assert(result as int == Self::coin_change_ways(coins@, i as nat, a as int));
        }
        let ghost pre_memo = memo@;
        memo.set(idx, result);
        proof {
            assert(memo@ == pre_memo.update(idx as int, result));
            assert(memo@.len() == (coins.len() as int + 1) * width as int);
            assert forall |ii: int, aa: int| 0 <= ii <= coins.len() as int && 0 <= aa < width as int &&
                #[trigger] memo@[ii * width as int + aa] != -1
                implies memo@[ii * width as int + aa] as int == Self::coin_change_ways(coins@, ii as nat, aa)
            by {
                let jdx = ii * width as int + aa;
                Self::lemma_idx_bound(coins.len() as int, width as int, ii, aa);
                assert(0 <= jdx < memo@.len());
                if jdx == idx as int {
                    Self::lemma_idx_unique(width as int, ii, aa, i as int, a as int);
                } else {
                    assert(memo@[jdx] == pre_memo[jdx]);
                }
            }
        }
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
        proof {
            assert((coins.len() + 1) * width <= 301 * 5001) by (nonlinear_arith)
                requires
                    coins.len() <= 300,
                    width <= 5001,
            {}
        }
        let total_len = (coins.len() + 1) * width;
        let mut memo: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < total_len
            invariant
                0 <= k <= total_len,
                memo.len() == k,
                forall |idx: int| 0 <= idx < k ==> memo@[idx] == -1,
            decreases total_len - k,
        {
            memo.push(-1);
            k += 1;
        }
        proof {
            assert forall |ii: int, aa: int| 0 <= ii <= coins.len() as int && 0 <= aa < width as int &&
                #[trigger] memo@[ii * width as int + aa] != -1
                implies memo@[ii * width as int + aa] as int == Self::coin_change_ways(coins@, ii as nat, aa)
            by {
                Self::lemma_idx_bound(coins.len() as int, width as int, ii, aa);
                assert(memo@[ii * width as int + aa] == -1);
            }
        }
        Self::coin_rec(&coins, coins.len(), amount as usize, &mut memo, width)
    }
}

}
