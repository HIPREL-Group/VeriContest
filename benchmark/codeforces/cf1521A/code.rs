impl Solution {
    pub fn construct_numbers(a: i64, b: i64) -> (bool, i64, i64, i64) {
        if b == 1 {
            (false, 0, 0, 0)
        } else {
            let x = a;
            let y = a * b;
            let z = a * (b + 1);
            (true, x, y, z)
        }
    }
}
