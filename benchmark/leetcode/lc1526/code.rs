impl Solution {
    pub fn min_number_operations(target: Vec<i32>) -> i32 {
        let n = target.len();
        let mut ops: i32 = target[0];
        for i in 1..n
        {
            if target[i] > target[i - 1] {
                ops = ops + (target[i] - target[i - 1]);
            }
        }
        ops
    }
}
