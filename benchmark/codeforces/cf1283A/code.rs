impl Solution {
    pub fn minutes_before_new_year_one(h: i32, m: i32) -> i32 {
        let result = (1440i64 - 60i64 * (h as i64) - (m as i64)) as i32;
        result
    }
}
