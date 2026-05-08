impl Solution {
    pub fn maximum_score(a: i32, b: i32, c: i32) -> i32 {
        let mx = if a >= b && a >= c { a } else if b >= c { b } else { c };
        let s = a + b + c;
        if mx >= s - mx {
            s - mx
        } else {
            s / 2
        }
    }
}
