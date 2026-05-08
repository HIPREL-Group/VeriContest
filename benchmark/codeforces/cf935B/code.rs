impl Solution {
    pub fn fafa_and_gates(n: usize, s: Vec<i32>) -> i32 {
        let mut x = 0;
        let mut y = 0;
        let mut coins = 0;
        let mut i = 0;

        while i < n {
            let nxt = s[i];
            if i > 0 && x == y && s[i - 1] == nxt {
                coins += 1;
            }
            if nxt == 1 {
                x += 1;
            } else {
                y += 1;
            }
            i += 1;
        }

        coins
    }
}
