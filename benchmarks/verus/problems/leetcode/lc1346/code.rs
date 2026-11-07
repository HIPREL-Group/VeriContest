impl Solution {
    pub fn check_if_exist(arr: Vec<i32>) -> bool {
        let n = arr.len();
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < n {
                if i != j && arr[i] == 2 * arr[j] {
                    return true;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        false
    }
}
