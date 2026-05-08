impl Solution {
    pub fn arrange_coins(n: i32) -> i32
    {
        let mut step: i32 = 0;
        let mut remaining: i32 = n;
        
        while remaining > step && step < 65535
        {
            step = step + 1;
            remaining = remaining - step;
        }
        
        step
    }
}
