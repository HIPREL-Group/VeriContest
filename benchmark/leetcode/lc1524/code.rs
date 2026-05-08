impl Solution {
    pub fn num_of_subarrays(arr: Vec<i32>) -> i32 {
        let mut odd: i64 = 0;
        let mut even: i64 = 0;
        let mut res: i64 = 0;
        let mut i: usize = 0;
        while i < arr.len() {
            if arr[i] % 2 == 0 {
                even = even + 1;
            } else {
                let tmp = odd;
                odd = even + 1;
                even = tmp;
            }
            res = (res + odd) % 1_000_000_007i64;
            i = i + 1;
        }
        res as i32
    }
}
