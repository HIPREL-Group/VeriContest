impl Solution {
    pub fn stone_game_viii(stones: Vec<i32>) -> i32 {
        let n = stones.len();
        let mut prefix: Vec<i64> = Vec::new();
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum + stones[i] as i64;
            prefix.push(sum);
            i += 1;
        }
        let mut dp: i64 = prefix[n - 1];
        let mut j: usize = n - 2;
        while j >= 1 {
            let pick = prefix[j] - dp;
            if pick > dp {
                dp = pick;
            }
            j -= 1;
        }
        dp as i32
    }
}
