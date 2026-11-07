impl Solution {
    pub fn trailing_zeroes(n: i32) -> i32
    {
        let mut remaining = n;
        let mut count = 0;
        while remaining > 0
        {
            remaining = remaining / 5;
            count = count + remaining;
        }
        count
    }
}
