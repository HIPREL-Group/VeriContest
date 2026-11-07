impl Solution {
    pub fn find_kth_positive(arr: Vec<i32>, k: i32) -> i32 {
        let mut missing: i32 = 0;
        let mut current: i32 = 1;
        let mut idx: usize = 0;
        while missing < k {
            if idx < arr.len() && arr[idx] == current {
                idx = idx + 1;
            } else {
                missing = missing + 1;
            }
            current = current + 1;
        }
        current - 1
    }
}
