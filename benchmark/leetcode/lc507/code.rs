impl Solution {
    pub fn get_sum(n: i32) -> i64
    {
        let mut sum: i64 = 0;
        let mut i: i32 = 1;
        
        while i < n
        {
            if n % i == 0 {
                sum = sum + i as i64;
            }
            
            i = i + 1;
        }
        
        sum
    }

    pub fn check_perfect_number(num: i32) -> bool
    {
        if (num as i64) == Self::get_sum(num) {
            true
        }
        else {
            false
        }
    }
}
