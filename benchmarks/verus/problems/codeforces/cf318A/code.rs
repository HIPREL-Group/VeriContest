impl Solution {
    pub fn kth_even_odds(n: u64, k: u64) -> u64 {
        let count_odds = (n + 1) / 2;
        if k <= count_odds {
            2 * k - 1
        } else {
            2 * (k - count_odds)
        }
    }
}
