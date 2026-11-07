impl Solution {
    pub fn final_x_value(operations: Vec<i32>) -> i32 {
        let mut sum = 0i32;
        let n = operations.len();
        let mut i = 0usize;
        while i < n {
            sum = sum + operations[i];
            i = i + 1;
        }
        sum
    }
}
