impl Solution {
    fn coin_rec(coins: &Vec<i32>, i: usize, a: usize, memo: &mut Vec<i32>, width: usize) -> i32 {
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
        memo[idx] = result;
        result
    }

    pub fn change(amount: i32, coins: Vec<i32>) -> i32 {
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
