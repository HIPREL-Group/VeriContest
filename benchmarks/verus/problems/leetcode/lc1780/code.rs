impl Solution {
    pub fn check_powers_of_three(n: i32) -> bool {
        let mut cur = n;
        while cur > 0 {
            if cur % 3 == 2 {
                return false;
            }
            cur = cur / 3;
        }
        true
    }
}
