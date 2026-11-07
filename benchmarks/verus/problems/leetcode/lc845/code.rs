impl Solution {
    pub fn longest_mountain(arr: Vec<i32>) -> i32 {
        let n = arr.len();
        if n < 3 {
            return 0;
        }
        let mut best: i32 = 0;
        let mut up: usize = 0;
        let mut down: usize = 0;
        let mut i: usize = 1;
        while i < n {
            if arr[i] > arr[i - 1] {
                if down > 0 {
                    up = 0;
                    down = 0;
                }
                up = up + 1;
            } else if arr[i] < arr[i - 1] {
                if up > 0 {
                    down = down + 1;
                }
            } else {
                up = 0;
                down = 0;
            }
            if up > 0 && down > 0 {
                let len = (up + down + 1) as i32;
                if len > best {
                    best = len;
                }
            }
            i = i + 1;
        }
        best
    }
}
