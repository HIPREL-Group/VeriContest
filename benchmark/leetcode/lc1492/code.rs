impl Solution {
    pub fn kth_factor(n: i32, k: i32) -> i32 {
        let mut count: i32 = 0;
        let mut i: i32 = 1;
        while i <= n {
            if n % i == 0 {
                count = count + 1;
                if count == k {
                    return i;
                }
            }
            i = i + 1;
        }
        -1
    }
}
