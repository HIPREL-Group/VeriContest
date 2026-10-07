impl Solution {
    pub fn two_sum(nums: Vec<i32>, target: i32) -> Vec<i32> {
        let mut res: Vec<i32> = vec![0, 1];
        let mut found = false;

        let mut left = 0;
        while left < nums.len() && !found {
            let mut right = left + 1;
            while right < nums.len() && !found {
                if nums[left] + nums[right] == target {
                    res[0] = left as i32;
                    res[1] = right as i32;
                    found = true;
                }
                right += 1;
            }
            left += 1;
        }
        res
    }
}
