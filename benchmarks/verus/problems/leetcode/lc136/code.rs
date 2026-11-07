impl Solution {
    pub fn single_number(nums: Vec<i32>) -> i32
    {
        let mut no: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len()
        {
            no = no ^ nums[i];
            i = i + 1;
        }
        return no
    }
}
