impl Solution {
    pub fn chocolate_ways(n: usize, a: Vec<i32>) -> i128 {
        let mut ans: u128 = 1;
        let mut prev: i64 = -1;
        let mut seen: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 1 {
                if prev >= 0 {
                    let gap = i as u128 - prev as u128;
                    ans = ans * gap;
                }
                prev = i as i64;
                seen = seen + 1;
            }
            i = i + 1;
        }
        if seen == 0 {
            0
        } else if seen == 1 {
            1
        } else {
            ans as i128
        }
    }
}
