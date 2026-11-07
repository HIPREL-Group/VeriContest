impl Solution {
    pub fn is_dividing_number(n: i32) -> bool
    {
        let mut num = n;
        while num > 0 
        {
            let digit = num % 10;
            if digit == 0 || n % digit != 0 {
                return false;
            }
            num = num / 10;
        }
        true
    }

    pub fn self_dividing_numbers(left: i32, right: i32) -> Vec<i32>
    {
        let mut result: Vec<i32> = Vec::new();
        let mut current = left;
        
        while current <= right
        {
            if Self::is_dividing_number(current) {                
                result.push(current);
            } 
            current = current + 1;
        }
        
        result
    }
}
