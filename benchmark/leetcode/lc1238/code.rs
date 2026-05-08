impl Solution {
    pub fn circular_permutation(n: i32, start: i32) -> Vec<i32> {
        let n_u = n as u32;
        let total = 1i32 << n_u;
        let mut result: Vec<i32> = Vec::new();
        let mut i: i32 = 0;
        while i < total {
            let gray_i = i ^ (i >> 1u32);
            let val = start ^ gray_i;
            result.push(val);
            i = i + 1;
        }
        result
    }
}
