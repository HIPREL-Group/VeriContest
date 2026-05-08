impl Solution {
    pub fn max_passengers(exits: Vec<i32>, entries: Vec<i32>) -> i32 {
        let n = exits.len();
        let mut max_val = 0i32;
        let mut current = 0i32;
        let mut i = 0usize;
        while i < n {
            current = current - exits[i] + entries[i];
            if current > max_val {
                max_val = current;
            }
            i += 1;
        }
        max_val
    }
}
