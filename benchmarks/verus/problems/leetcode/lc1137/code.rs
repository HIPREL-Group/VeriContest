impl Solution {
    pub fn tribonacci(n: i32) -> i32
    {
        if n == 0 {
            return 0;
        }
        else if n == 1 {
            return 1;
        }
        let mut prev1: i32 = 0;
        let mut prev2: i32 = 1;
        let mut cur: i32 = 1;

        let mut i: i32 = 2;
        while i < n
        {
            i = i + 1;
            let new_cur = cur + prev1 + prev2;
            prev1 = prev2; 
            prev2 = cur;
            cur = new_cur;
        }
        cur
    }
}
