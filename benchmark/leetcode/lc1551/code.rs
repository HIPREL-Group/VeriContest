impl Solution {
    pub fn min_operations(n: i32) -> i32 {
        let mut ops: i32 = 0;
        let mut i: i32 = 0;
        let limit = n / 2;
        
        while i < limit {
            ops += n - (2 * i + 1);
            i += 1;
        }
        
        ops
    }
}
