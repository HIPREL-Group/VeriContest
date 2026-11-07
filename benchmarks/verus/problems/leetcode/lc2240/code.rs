impl Solution {
    pub fn ways_to_buy_pens_pencils(total: i32, cost1: i32, cost2: i32) -> i64 {
        let t = total as i64;
        let c1 = cost1 as i64;
        let c2 = cost2 as i64;
        let max_pens = t / c1;
        let mut pens: i64 = 0;
        let mut ans: i64 = 0;
        while pens <= max_pens {
            ans = ans + (t - pens * c1) / c2 + 1;
            pens = pens + 1;
        }
        ans
    }
}
