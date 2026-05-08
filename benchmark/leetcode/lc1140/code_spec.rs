use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_sum(piles: Seq<i32>, i: int) -> int
        decreases piles.len() - i
    {
        if i >= piles.len() {
            0
        } else {
            piles[i] as int + Self::suffix_sum(piles, i + 1)
        }
    }

    pub open spec fn game(piles: Seq<i32>, i: int, m: int, k: int) -> int
        decreases piles.len() - i, k
        when m >= 1 && k >= 0 && i >= 0
            && (1 <= k && k <= 2 * m ==> i + 2 * m < piles.len())
    {
        if k > 2 * m {
            if i >= piles.len() {
                0
            } else if i + 2 * m >= piles.len() {
                Self::suffix_sum(piles, i)
            } else {
                Self::game(piles, i, m, 2 * m)
            }
        } else if k == 0 {
            0
        } else {
            let new_m = if k > m { k } else { m };
            let score_k = Self::suffix_sum(piles, i)
                - Self::game(piles, i + k, new_m, 2 * new_m + 1);
            if k == 1 {
                score_k
            } else {
                let prev = Self::game(piles, i, m, k - 1);
                if score_k >= prev { score_k } else { prev }
            }
        }
    }

    pub open spec fn optimal(piles: Seq<i32>, i: int, m: int) -> int
    {
        Self::game(piles, i, m, 2 * m + 1)
    }

    pub open spec fn max_score(piles: Seq<i32>, i: int, m: int, k: int) -> int
    {
        Self::game(piles, i, m, k)
    }

    pub fn stone_game_ii(piles: Vec<i32>) -> (result: i32)
        requires
            1 <= piles.len() <= 100,
            forall |i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
        ensures
            result as int == Self::optimal(piles@, 0, 1),
    {
        let n = piles.len();
        let stride = n + 1;
        let mut suffix_sums: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < stride {
            suffix_sums.push(0i32);
            k += 1;
        }
        let mut si = n;
        while si > 0 {
            si -= 1;
            suffix_sums.set(si, suffix_sums[si + 1] + piles[si]);
        }
        let total = stride * stride;
        let mut dp: Vec<i32> = Vec::new();
        let mut k2: usize = 0;
        while k2 < total {
            dp.push(0i32);
            k2 += 1;
        }
        let mut i: usize = n;
        while i > 0 {
            i -= 1;
            let mut m: usize = 1;
            while m <= n {
                if i + 2 * m >= n {
                    dp.set(i * stride + m, suffix_sums[i]);
                } else {
                    let mut best: i32 = suffix_sums[i] - dp[(i + 1) * stride + m];
                    let mut x: usize = 2;
                    while x <= 2 * m {
                        let new_m: usize = if x > m { x } else { m };
                        let score: i32 = suffix_sums[i] - dp[(i + x) * stride + new_m];
                        if score > best {
                            best = score;
                        }
                        x += 1;
                    }
                    dp.set(i * stride + m, best);
                }
                m += 1;
            }
        }
        dp[1]
    }
}

}
