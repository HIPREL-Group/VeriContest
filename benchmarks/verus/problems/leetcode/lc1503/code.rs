impl Solution {
    pub fn get_last_moment(n: i32, left: Vec<i32>, right: Vec<i32>) -> i32 {
        let mut max_left: i32 = 0;
        let mut i: usize = 0;
        while i < left.len() {
            if left[i] >= max_left {
                max_left = left[i];
            }
            i = i + 1;
        }
        let mut min_right: i32 = n;
        let mut j: usize = 0;
        while j < right.len() {
            if right[j] <= min_right {
                min_right = right[j];
            }
            j = j + 1;
        }
        if max_left >= n - min_right {
            max_left
        } else {
            n - min_right
        }
    }
}
