impl Solution {
    pub fn find_special_integer(arr: Vec<i32>) -> i32 {
        let n = arr.len();
        let quarter = n / 4;
        let mut i: usize = 0;
        while i + quarter < n {
            if arr[i] == arr[i + quarter] {
                return arr[i];
            }
            i += 1;
        }
        arr[0]
    }
}
