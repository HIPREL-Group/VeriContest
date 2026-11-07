impl Solution {
    pub fn exact_damage_possible(a: i32, b: i32, c: i32) -> bool {
        let mut x: i32 = 0;
        while x <= c {
            if x > c / a {
                break;
            }
            let rem = c - x * a;
            if rem % b == 0 {
                return true;
            }
            x = x + 1;
        }
        false
    }
}
