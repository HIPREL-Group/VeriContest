impl Solution {
    pub fn total_road_width(a: Vec<i32>, n: usize, h: i32) -> i32 {
        let mut sum = 0i32;
        let mut i = 0usize;
        while i < n {
            if a[i] <= h {
                sum += 1;
            } else {
                sum += 2;
            }
            i += 1;
        }
        sum
    }
}
