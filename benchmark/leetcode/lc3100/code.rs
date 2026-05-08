impl Solution {
    pub fn max_bottles_drunk(num_bottles: i32, num_exchange: i32) -> i32 {
        let mut ans = num_bottles;
        let mut empty = num_bottles;
        let mut exchange = num_exchange;
        while empty >= exchange {
            empty = empty - exchange + 1;
            exchange = exchange + 1;
            ans = ans + 1;
        }
        ans
    }
}
