impl Solution {
    pub fn min_deletion(nums: Vec<i32>) -> i32 {
        let mut d: i64 = 0;
        let mut i: usize = 0;

        while i + 1 < nums.len() {
            if ((i as i64 - d) % 2 == 0) && nums[i] == nums[i + 1] {
                d = d + 1;
            }
            i = i + 1;
        }

        if ((nums.len() as i64 - d) % 2) == 1 {
            d = d + 1;
        }

        d as i32
    }
}
