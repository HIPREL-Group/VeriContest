impl Solution {
    pub fn can_make_beautiful(a: i32, b: i32, c: i32, d: i32) -> bool {
        (a < b && c < d && a < c && b < d)
            || (c < a && d < b && c < d && a < b)
            || (d < c && b < a && d < b && c < a)
            || (b < d && a < c && b < a && d < c)
    }
}
