impl Solution {
    pub fn min_taps(n: i32, ranges: Vec<i32>) -> i32 {
        let mut max_reach: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n as usize {
            max_reach.push(0i32);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i <= n as usize {
            let r = ranges[i];
            if r > 0 {
                let left: usize = if (i as i32) >= r { i - r as usize } else { 0 };
                let right: i32 = i as i32 + r;
                if right > max_reach[left] {
                    max_reach[left] = right;
                }
            }
            i = i + 1;
        }

        let mut end: i32 = 0;
        let mut far: i32 = 0;
        let mut cnt: i32 = 0;

        let mut j: usize = 0;
        while j <= n as usize {
            if j as i32 > end {
                return -1;
            }
            if max_reach[j] > far {
                far = max_reach[j];
            }
            if j as i32 == end && end < n {
                if far <= end {
                    return -1;
                }
                end = far;
                cnt = cnt + 1;
            }
            j = j + 1;
        }

        cnt
    }
}
