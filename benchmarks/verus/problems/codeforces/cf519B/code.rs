impl Solution {
    pub fn find_compilation_errors(first: Vec<i64>, second: Vec<i64>, third: Vec<i64>) -> (i64, i64) {
        let mut sum_first: i64 = 0;
        let mut i: usize = 0;
        while i < first.len() {
            sum_first = sum_first + first[i];
            i = i + 1;
        }

        let mut sum_second: i64 = 0;
        let mut j: usize = 0;
        while j < second.len() {
            sum_second = sum_second + second[j];
            j = j + 1;
        }

        let mut sum_third: i64 = 0;
        let mut k: usize = 0;
        while k < third.len() {
            sum_third = sum_third + third[k];
            k = k + 1;
        }

        let deleted_first = sum_first - sum_second;
        let deleted_second = sum_second - sum_third;
        (deleted_first, deleted_second)
    }
}
