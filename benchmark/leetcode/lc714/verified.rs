use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn spec_cash(prices: Seq<i32>, fee: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::spec_max(
                Self::spec_cash(prices, fee, i - 1),
                Self::spec_hold(prices, fee, i - 1) + prices[i] as int - fee
            )
        }
    }

    pub open spec fn spec_hold(prices: Seq<i32>, fee: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            -(prices[0] as int)
        } else {
            Self::spec_max(
                Self::spec_hold(prices, fee, i - 1),
                Self::spec_cash(prices, fee, i - 1) - prices[i] as int
            )
        }
    }

    proof fn spec_cash_nonneg(prices: Seq<i32>, fee: int, i: int)
        requires
            0 <= i < prices.len(),
            forall |k: int| 0 <= k < prices.len() ==> 1 <= #[trigger] prices[k] < 50_000,
            0 <= fee < 50_000,
        ensures
            Self::spec_cash(prices, fee, i) >= 0,
        decreases i,
    {
        if i > 0 {
            Self::spec_cash_nonneg(prices, fee, i - 1);
            Self::spec_hold_lower(prices, fee, i - 1);
        }
    }

    proof fn spec_hold_lower(prices: Seq<i32>, fee: int, i: int)
        requires
            0 <= i < prices.len(),
            forall |k: int| 0 <= k < prices.len() ==> 1 <= #[trigger] prices[k] < 50_000,
            0 <= fee < 50_000,
        ensures
            Self::spec_hold(prices, fee, i) >= -50_000,
        decreases i,
    {
        if i > 0 {
            Self::spec_hold_lower(prices, fee, i - 1);
            Self::spec_cash_nonneg(prices, fee, i - 1);
        }
    }

    proof fn spec_hold_le_prev_cash(prices: Seq<i32>, fee: int, i: int)
        requires
            0 <= i < prices.len(),
            forall |k: int| 0 <= k < prices.len() ==> 1 <= #[trigger] prices[k] < 50_000,
            0 <= fee < 50_000,
        ensures
            i == 0 ==> Self::spec_hold(prices, fee, i) <= 0,
            i > 0 ==> Self::spec_hold(prices, fee, i) <= Self::spec_cash(prices, fee, i - 1),
        decreases i,
    {
        if i > 0 {
            Self::spec_hold_le_prev_cash(prices, fee, i - 1);
            Self::spec_cash_nonneg(prices, fee, i - 1);
        }
    }

    proof fn spec_cash_upper(prices: Seq<i32>, fee: int, i: int)
        requires
            0 <= i < prices.len(),
            prices.len() <= 50_000,
            forall |k: int| 0 <= k < prices.len() ==> 1 <= #[trigger] prices[k] < 50_000,
            0 <= fee < 50_000,
        ensures
            Self::spec_cash(prices, fee, i) <= 25_000 * (i + 1),
        decreases i,
    {
        if i > 0 {
            Self::spec_cash_upper(prices, fee, i - 1);
            Self::spec_hold_le_prev_cash(prices, fee, i - 1);
            if i >= 2 {
                Self::spec_cash_upper(prices, fee, i - 2);
            }
        }
    }

    proof fn spec_hold_upper(prices: Seq<i32>, fee: int, i: int)
        requires
            0 <= i < prices.len(),
            prices.len() <= 50_000,
            forall |k: int| 0 <= k < prices.len() ==> 1 <= #[trigger] prices[k] < 50_000,
            0 <= fee < 50_000,
        ensures
            Self::spec_hold(prices, fee, i) <= 25_000 * (i + 1),
    {
        Self::spec_hold_le_prev_cash(prices, fee, i);
        if i > 0 {
            Self::spec_cash_upper(prices, fee, i - 1);
        }
    }

    pub fn max_profit(prices: Vec<i32>, fee: i32) -> (res: i32)
        requires
            1 <= prices.len() <= 50_000,
            forall |i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] < 50_000,
            0 <= fee < 50_000,
        ensures
            res as int == Self::spec_cash(prices@, fee as int, (prices.len() - 1) as int),
    {
        let ghost p = prices@;
        let ghost f = fee as int;
        let mut cash: i32 = 0;
        let mut hold: i32 = -prices[0];
        let n = prices.len();
        for i in 1..n
            invariant
                n == prices.len(),
                n <= 50_000,
                p == prices@,
                f == fee as int,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] prices[k] < 50_000,
                0 <= fee < 50_000,
                cash as int == Self::spec_cash(p, f, (i - 1) as int),
                hold as int == Self::spec_hold(p, f, (i - 1) as int),
                0 <= cash <= 25_000 * i,
                -50_000 <= hold <= 25_000 * i,
        {
            proof {
                Self::spec_cash_nonneg(p, f, i as int);
                Self::spec_cash_upper(p, f, i as int);
                Self::spec_hold_lower(p, f, i as int);
                Self::spec_hold_upper(p, f, i as int);
            }
            let prev_cash = cash;
            let prev_hold = hold;
            if prev_hold + prices[i] - fee > prev_cash {
                cash = prev_hold + prices[i] - fee;
            }
            if prev_cash - prices[i] > prev_hold {
                hold = prev_cash - prices[i];
            }
        }
        cash
    }
}

}
