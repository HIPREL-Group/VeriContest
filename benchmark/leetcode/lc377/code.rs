impl Solution {
    fn combo_rec(nums: &Vec<i32>, t: usize) -> i32 {
        if t == 0 {
            return 1;
        }
        let mut total: i32 = 0;
        let mut j: usize = 0;
        while j < nums.len() {
            let num = nums[j];
            if (num as usize) <= t {
                let sub = Self::combo_rec(nums, t - num as usize);
                total = total + sub;
            }
            j += 1;
        }
        total
    }

    pub fn combination_sum4(nums: Vec<i32>, target: i32) -> i32 {
        Self::combo_rec(&nums, target as usize)
    }
}
