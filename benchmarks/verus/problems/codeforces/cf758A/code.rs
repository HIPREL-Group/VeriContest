impl Solution {
    pub fn holiday_equality_burles(n: usize, a: Vec<i32>) -> i32 {
        let mut maxv = a[0];
        let mut i = 1usize;
        while i < n {
            if a[i] > maxv {
                maxv = a[i];
            }
            i += 1;
        }
        let mut sum = 0i32;
        let mut j = 0usize;
        while j < n {
            sum += maxv - a[j];
            j += 1;
        }
        sum
    }
}
