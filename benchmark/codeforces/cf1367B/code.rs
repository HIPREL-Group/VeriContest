impl Solution {
    pub fn min_swaps(n: usize, a: Vec<u32>) -> i64 {
        let mut odd_at_even: i64 = 0;
        let mut even_at_odd: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if i % 2 == 0 && a[i] % 2 == 1 {
                odd_at_even += 1;
            } else if i % 2 == 1 && a[i] % 2 == 0 {
                even_at_odd += 1;
            }
            i += 1;
        }
        if odd_at_even == even_at_odd {
            odd_at_even
        } else {
            -1
        }
    }
}
