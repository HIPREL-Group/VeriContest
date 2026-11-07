impl Solution {
    pub fn replace_elements(arr: Vec<i32>) -> Vec<i32> {
        let mut result = arr;
        let n = result.len();
        let mut max_right: i32 = -1;
        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            let current = result[i];
            result[i] = max_right;
            if current > max_right {
                max_right = current;
            }
        }
        result
    }
}
