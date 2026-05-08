impl Solution {
    pub fn climb_stairs(n: i32) -> i32
    {
        let mut prev: i32 = 0;
        let mut cur: i32 = 1;
        let mut i: i32 = 1;
        while i <= n
        {
            i = i + 1;
            let new_cur = cur + prev;
            prev = cur;
            cur = new_cur;
        }
        cur
    }
}
