impl Solution {
    pub fn three_consecutive_odds(arr: Vec<i32>) -> bool {
        let n = arr.len();
        let mut i: usize = 0;
        while i + 2 < n {
            if arr[i] % 2 == 1 && arr[i + 1] % 2 == 1 && arr[i + 2] % 2 == 1 {
                return true;
            }
            i = i + 1;
        }
        false
    }
}
