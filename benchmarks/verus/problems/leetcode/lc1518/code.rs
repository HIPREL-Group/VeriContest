impl Solution {
    pub fn num_water_bottles(num_bottles: i32, num_exchange: i32) -> i32 {
        let mut ans: i32 = num_bottles;
        let mut empty: i32 = num_bottles;
        
        while empty >= num_exchange {
            let full = empty / num_exchange;
            let next_empty = full + (empty % num_exchange);
            
            ans += full;
            empty = next_empty;
        }
        
        ans
    }
}
