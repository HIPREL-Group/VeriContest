impl Solution {
    pub fn can_jump(nums: Vec<i32>) -> bool
    {
        let len = nums.len();
        let mut furthest_reachable = 0;

        for i in 0..len
        {
            if i > furthest_reachable {
                return false;
            }
            let new_reach = i + nums[i] as usize;
            if new_reach > furthest_reachable {
                furthest_reachable = new_reach;
            }
        }

        true
    }
}
