impl Solution {
    pub fn min_operations(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut a = nums.clone();
        let mut ans = 0i32;
        let mut i = 0usize;
        while i + 2 < n {
            if a[i] == 0 {
                a[i] = 1;
                a[i + 1] = if a[i + 1] == 0 { 1 } else { 0 };
                a[i + 2] = if a[i + 2] == 0 { 1 } else { 0 };
                ans = ans.checked_add(1).unwrap_or(ans);
            }
            i += 1;
        }
        if a[n - 1] == 0 || a[n - 2] == 0 {
            -1
        } else {
            ans
        }
    }
}
