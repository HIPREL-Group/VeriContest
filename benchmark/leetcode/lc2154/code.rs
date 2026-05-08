impl Solution {
    pub fn find_final_value(nums: Vec<i32>, original: i32) -> i32 {
        let mut current = original;
        let mut found = true;
        while found {
            found = false;
            let mut i = 0;
            while i < nums.len() {
                if nums[i] == current {
                    found = true;
                }
                i += 1;
            }
            if found {
                current *= 2;
            }
        }
        current
    }
}
