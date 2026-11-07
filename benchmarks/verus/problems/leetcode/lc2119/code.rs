impl Solution {
    pub fn is_same_after_reversals(num: i32) -> bool
    {
        let mut n = num;
        let mut reversed1 = 0i32;
        
        while n > 0
        {
            reversed1 = reversed1 * 10 + n % 10;
            n = n / 10;
        }
        
        let mut m = reversed1;
        let mut reversed2 = 0i32;
        
        while m > 0
        {
            reversed2 = reversed2 * 10 + m % 10;
            m = m / 10;
        }
        
        reversed2 == num
    }
}
