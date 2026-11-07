impl Solution {
    pub fn single_non_duplicate(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let mut i: usize = 0;
        while i + 1 < n
        {
            if nums[i] != nums[i + 1] {
                let result = nums[i];
                return result;
            }
            i = i + 2;
        }
        nums[i]
    }
}
