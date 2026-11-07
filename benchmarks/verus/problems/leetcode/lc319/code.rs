impl Solution {
    pub fn bulb_switch(n: i32) -> i32 {
        let mut i: i32 = 0;
        loop
        {
            if (i as i64 + 1) * (i as i64 + 1) > n as i64 {
                break;
            }
            i += 1;
        }
        i
    }
}
