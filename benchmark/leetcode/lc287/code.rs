impl Solution {
    pub fn find_duplicate(nums: Vec<i32>) -> i32
    {
        let mut numTrack: [bool;100001] = [false;100001];

        let mut i = 0;
        while i < nums.len()
        {
            if numTrack[nums[i] as usize] {
                return nums[i];
            }
            else {
                numTrack[nums[i] as usize] = true;
            }
            i += 1;
        }
        return 0 
    }
}
