impl Solution {
    pub fn find_latest_step(arr: Vec<i32>, m: i32) -> i32
    {
        let n = arr.len();

        let mut length: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n + 2 {
            length.push(0);
            idx = idx + 1;
        }

        let mut count_m: i32 = 0;
        let mut res: i32 = -1;

        let mut i: usize = 0;
        while i < n {
            let a = arr[i] as usize;
            let left = length[a - 1];
            let right = length[a + 1];
            let new_len = left + right + 1;

            length[a - left as usize] = new_len;
            length[a + right as usize] = new_len;

            if left == m {
                count_m = count_m - 1;
            }
            if right == m {
                count_m = count_m - 1;
            }
            if new_len == m {
                count_m = count_m + 1;
            }

            if count_m > 0 {
                res = (i + 1) as i32;
            }

            i = i + 1;
        }

        res
    }
}
