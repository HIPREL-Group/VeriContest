impl Solution {
    pub fn sum_of_three(num: i64) -> Vec<i64> {
        if num % 3 != 0 {
            return Vec::new();
        }

        let mid = num / 3;
        let out = vec![mid - 1, mid, mid + 1];
        out
    }
}
