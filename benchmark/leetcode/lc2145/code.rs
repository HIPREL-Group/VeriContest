impl Solution {
    pub fn number_of_arrays(differences: Vec<i32>, lower: i32, upper: i32) -> i32 {
        let n = differences.len();
        let mut i: usize = 0;
        let mut cur: i128 = 0;
        let mut min_p: i128 = 0;
        let mut max_p: i128 = 0;

        while i < n {
            cur = cur + differences[i] as i128;
            if cur < min_p {
                min_p = cur;
            }
            if max_p < cur {
                max_p = cur;
            }
            i = i + 1;
        }

        let width: i128 = (upper as i128) - (lower as i128);
        let span: i128 = max_p - min_p;
        if span > width {
            0
        } else {
            let ans: i128 = width - span + 1;
            ans as i32
        }
    }
}
