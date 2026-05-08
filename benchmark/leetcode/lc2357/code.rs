impl Solution {
    pub fn minimum_operations(nums: Vec<i32>) -> i32
    {
        let mut freqs: [bool; 101] = [false;101];

        for i in 0..nums.len()
        {
            freqs[nums[i] as usize] = true;
        }

        let mut ans: u8 = 0;
        for idx in 1..101
        {
            if freqs[idx] == true {
                ans += 1;
            }
        }
        ans as i32
    }
}
