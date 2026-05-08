impl Solution {
    pub fn peak_index_in_mountain_array(arr: Vec<i32>) -> i32 {
        let n = arr.len();
        let mut left: usize = 0;
        let mut right: usize = n - 1;
        while left < right {
            let mid = left + (right - left) / 2;
            if arr[mid] < arr[mid + 1] {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        left as i32
    }
}
