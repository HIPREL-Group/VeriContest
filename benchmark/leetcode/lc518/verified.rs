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

    proof fn lemma_ways_unchanged_below_coin(coins: Seq<i32>, coins_used: nat, amount: int)
        requires
            coins_used > 0,
            coins_used <= coins.len(),
            0 <= amount < coins[(coins_used - 1) as int] as int,
        ensures
            Self::coin_change_ways(coins, coins_used, amount) == Self::coin_change_ways(coins, (coins_used - 1) as nat, amount),
    {
    }

    proof fn lemma_ways_recurrence(coins: Seq<i32>, coins_used: nat, amount: int)
        requires
            coins_used > 0,
            coins_used <= coins.len(),
            0 <= amount,
            1 <= coins[(coins_used - 1) as int] as int <= amount,
        ensures
            Self::coin_change_ways(coins, coins_used, amount)
                == Self::coin_change_ways(coins, (coins_used - 1) as nat, amount)
                    + Self::coin_change_ways(coins, coins_used, amount - (coins[(coins_used - 1) as int] as int)),
    {
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
        } else if coins_used <= coins.len() {
            let c = coins[(coins_used - 1) as int] as int;
            if 1 <= c <= amount {
                Self::lemma_ways_nonneg(coins, coins_used, amount - c);
                Self::lemma_ways_nonneg(coins, (coins_used - 1) as nat, amount);
            } else {
                Self::lemma_ways_nonneg(coins, (coins_used - 1) as nat, amount);
            }
        }
    }

    pub fn change(amount: i32, coins: Vec<i32>) -> (res: i32)
        requires
            0 <= amount <= 5000,
            1 <= coins.len() <= 300,
            forall |i: int| 0 <= i < coins.len() ==> 1 <= #[trigger] coins[i] <= 5000,
            forall |i: int, j: int| 0 <= i < j < coins.len() ==> coins[i] != coins[j],
            forall |i: nat, a: int|
                i <= coins.len() as nat && 0 <= a <= amount as int
                    ==> Self::coin_change_ways(coins@, i, a) <= i32::MAX,
            forall |i: nat, a: int|
                i <= (coins@).len() && 0 <= a <= amount as int
                    ==> #[trigger] Self::ways_bounded(coins@, amount as int, i, a),
        ensures
            res as int == Self::coin_change_ways(coins@, coins.len() as nat, amount as int),
    {
        let amount_usize = amount as usize;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= amount_usize
            invariant
                0 <= amount <= 5000,
                amount_usize == amount as usize,
                0 <= k <= amount_usize + 1,
                dp.len() == k,
                forall |idx: int| 0 <= idx < k ==> dp@[idx] == 0,
            decreases amount_usize + 1 - k,
        {
            dp.push(0);
            k += 1;
        }
        let ghost dp_init = dp@;
        dp.set(0, 1);
        proof {
            assert(dp@ == dp_init.update(0, 1));
            assert(dp@[0] as int == 1);
            assert(Self::coin_change_ways(coins@, 0, 0) == 1);
            assert forall |a: int| 1 <= a <= amount as int implies
                #[trigger] dp@[a] as int == Self::coin_change_ways(coins@, 0, a)
            by {
                if 1 <= a <= amount as int {
                    assert(0 <= a < (dp@).len());
                    assert(dp@[a] == dp_init[a]);
                    assert(dp_init[a] == 0);
                    assert(Self::coin_change_ways(coins@, 0, a) == 0);
                }
            }
        }
        proof {
            assert(forall |ii: nat, a: int|
                ii <= (coins@).len() && 0 <= a <= amount as int
                    ==> #[trigger] Self::ways_bounded(coins@, amount as int, ii, a));
        }
        let mut i: usize = 0;
        while i < coins.len()
            invariant
                0 <= amount <= 5000,
                1 <= coins.len() <= 300,
                amount_usize == amount as usize,
                dp.len() == amount_usize + 1,
                0 <= i <= coins.len(),
                forall |ii: int| 0 <= ii < coins.len() ==> 1 <= #[trigger] coins[ii] <= 5000,
                forall |a: int| 0 <= a <= amount as int ==> #[trigger] dp[a] as int == Self::coin_change_ways(coins@, i as nat, a),
                forall |ii: nat, a: int|
                    ii <= (coins@).len() && 0 <= a <= amount as int
                        ==> #[trigger] Self::ways_bounded(coins@, amount as int, ii, a),
            decreases coins.len() - i,
        {
            let coin = coins[i] as usize;
            proof {
                assert forall |a: int| 0 <= a < coin as int implies
                    Self::coin_change_ways(coins@, (i + 1) as nat, a)
                        == Self::coin_change_ways(coins@, i as nat, a)
                by {
                    Self::lemma_ways_unchanged_below_coin(coins@, (i + 1) as nat, a);
                }
                assert forall |a: int| 0 <= a < coin as int && a <= amount as int implies
                    #[trigger] dp@[a] as int == Self::coin_change_ways(coins@, (i + 1) as nat, a)
                by {
                    if 0 <= a < coin as int && a <= amount as int {
                        assert(0 <= a < (dp@).len());
                        assert(dp@[a] as int == Self::coin_change_ways(coins@, i as nat, a));
                        assert(Self::coin_change_ways(coins@, (i + 1) as nat, a)
                            == Self::coin_change_ways(coins@, i as nat, a));
                    }
                }
            }
            let mut j: usize = coin;
            while j <= amount_usize
                invariant
                    0 <= amount <= 5000,
                    amount_usize == amount as usize,
                    dp.len() == amount_usize + 1,
                    0 <= i < coins.len(),
                    coin == coins@[i as int] as usize,
                    coin <= j,
                    (coin <= amount_usize + 1) ==> j <= amount_usize + 1,
                    forall |ii: int| 0 <= ii < coins.len() ==> 1 <= #[trigger] coins[ii] <= 5000,
                    forall |a: int| 0 <= a < coin as int && a <= amount as int ==> #[trigger] dp[a] as int == Self::coin_change_ways(coins@, (i + 1) as nat, a),
                    forall |a: int| coin as int <= a < j as int ==> #[trigger] dp[a] as int == Self::coin_change_ways(coins@, (i + 1) as nat, a),
                    forall |a: int| j as int <= a <= amount as int ==> #[trigger] dp[a] as int == Self::coin_change_ways(coins@, i as nat, a),
                    forall |ii: nat, a: int|
                        ii <= (coins@).len() && 0 <= a <= amount as int
                            ==> #[trigger] Self::ways_bounded(coins@, amount as int, ii, a),
                decreases amount_usize + 1 - j,
            {
                let old_dp_j = dp[j];
                let add = dp[j - coin];
                proof {
                    Self::lemma_ways_recurrence(coins@, (i + 1) as nat, j as int);
                    assert(add as int == Self::coin_change_ways(coins@, (i + 1) as nat, (j as int) - (coins@[i as int] as int)));
                    assert(old_dp_j as int == Self::coin_change_ways(coins@, i as nat, j as int));
                    assert(0 <= i as int);
                    let seq_len = (coins@).len();
                    assert((i as int) < (seq_len as int));
                    assert(0 <= (j as int) - (coins@[i as int] as int));
                    assert((j as int) - (coins@[i as int] as int) <= amount as int);
                    assert((coins@[i as int] as int) <= j as int);
                    assert(j as int <= amount as int);
                    assert(Self::ways_bounded(coins@, amount as int, i as nat, j as int));
                    assert(Self::ways_bounded(
                        coins@,
                        amount as int,
                        (i + 1) as nat,
                        (j as int) - (coins@[i as int] as int),
                    ));
                    Self::lemma_ways_nonneg(coins@, (i + 1) as nat, j as int);
                    Self::lemma_ways_nonneg(coins@, i as nat, j as int);
                    Self::lemma_ways_nonneg(
                        coins@,
                        (i + 1) as nat,
                        (j as int) - (coins@[i as int] as int),
                    );
                    assert(0 <= old_dp_j);
                    assert(0 <= add);
                    assert(0 <= old_dp_j + add);
                    assert(old_dp_j + add <= i32::MAX);
                }
                dp.set(j, old_dp_j + add);
                proof {
                    assert(dp@[j as int] as int == Self::coin_change_ways(coins@, (i + 1) as nat, j as int));
                }
                j += 1;
            }
            proof {
                assert(forall |a: int| 0 <= a <= amount as int ==> dp[a] as int == Self::coin_change_ways(coins@, (i + 1) as nat, a));
            }
            i += 1;
        }
        proof {
            assert(i == coins.len());
            assert(forall |a: int| 0 <= a <= amount as int ==> dp[a] as int == Self::coin_change_ways(coins@, coins.len() as nat, a));
        }
        dp[amount_usize]
    }
}

}
