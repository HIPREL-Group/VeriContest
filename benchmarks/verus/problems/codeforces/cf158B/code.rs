impl Solution {
    pub fn min_taxis(c1: i32, c2: i32, c3: i32, c4: i32) -> i32 {
        let mut c1_rem = c1;
        let mut ans = c4;
        ans += c3;
        if c1_rem > c3 {
            c1_rem = c1_rem - c3;
        } else {
            c1_rem = 0;
        }
        ans += (c2 + 1) / 2;
        if c2 % 2 == 1 {
            if c1_rem > 2 {
                c1_rem = c1_rem - 2;
            } else {
                c1_rem = 0;
            }
        }
        ans += (c1_rem + 3) / 4;
        ans
    }
}
