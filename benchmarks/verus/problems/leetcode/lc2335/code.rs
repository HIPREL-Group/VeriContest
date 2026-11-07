impl Solution {
    pub fn fill_cups(amount: Vec<i32>) -> i32 {
        let a = amount[0];
        let b = amount[1];
        let c = amount[2];
        let m01 = if a > b { a } else { b };
        let m = if m01 > c { m01 } else { c };
        let s = a + b + c;
        let half = (s + 1) / 2;
        if m > half {
            m
        } else {
            half
        }
    }
}
