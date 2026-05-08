impl Solution {
    pub fn valid_mountain_array(arr: Vec<i32>) -> bool {
        let n = arr.len();
        if n < 3 {
            return false;
        }
        let mut i: usize = 0;
        while i + 1 < n && arr[i] < arr[i + 1] {
            i = i + 1;
        }
        if i == 0 {
            return false;
        }
        if i == n - 1 {
            return false;
        }
        let peak = i;
        while i + 1 < n && arr[i] > arr[i + 1] {
            i = i + 1;
        }
        if i == n - 1 {
            return true;
        } else {
            return false;
        }
    }
}
