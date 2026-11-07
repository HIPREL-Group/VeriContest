impl Solution {
    pub fn find_covering_segment(left: Vec<i32>, right: Vec<i32>) -> i32 {
        let mut candidate = 0usize;
        let mut i = 1usize;
        while i < left.len() {
            if left[i] < left[candidate] || (left[i] == left[candidate] && right[candidate] < right[i]) {
                candidate = i;
            }
            i += 1;
        }

        let mut j = 0usize;
        while j < left.len() {
            if left[candidate] > left[j] || right[j] > right[candidate] {
                return 0;
            }
            j += 1;
        }

        candidate as i32 + 1
    }
}
