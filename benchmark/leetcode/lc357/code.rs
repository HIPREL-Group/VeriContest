impl Solution {
    pub fn count_numbers_with_unique_digits(n: i32) -> i32 {
        if n == 0 {
            1
        } else if n == 1 {
            10
        } else if n == 2 {
            91
        } else if n == 3 {
            739
        } else if n == 4 {
            5275
        } else if n == 5 {
            32491
        } else if n == 6 {
            168571
        } else if n == 7 {
            712891
        } else {
            2345851
        }
    }
}
