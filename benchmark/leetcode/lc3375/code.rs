impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 {
        let mut i: usize = 0;
        while i < nums.len() {
            let x = nums[i];
            if x < k {
                return -1;
            }
            i = i + 1;
        }

        let mut ans: i32 = 0;
        let mut value: i32 = k + 1;
        while value <= 100 {
            let mut found: bool = false;
            let mut j: usize = 0;
            while j < nums.len() {
                if nums[j] == value {
                    found = true;
                }
                j = j + 1;
            }
            if found {
                ans = ans + 1;
            }
            value = value + 1;
        }

        ans
    }
}
