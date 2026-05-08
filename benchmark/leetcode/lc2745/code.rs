impl Solution {
    fn min2_exec(a: i32, b: i32) -> i32 {
        if a <= b { a } else { b }
    }

    pub fn longest_string(x: i32, y: i32, z: i32) -> i32 {
        (Self::min2_exec(x, y + 1) + Self::min2_exec(x + 1, y) + z) * 2
    }
}
