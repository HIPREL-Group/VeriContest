impl Solution {
    pub fn divide_array(nums: Vec<i32>) -> bool {
        let mut cnt: Vec<i32> = vec![0; 501];
        let mut i: usize = 0;
        while i < nums.len() {
            let x = nums[i] as usize;
            cnt[x] = cnt[x] + 1;
            i = i + 1;
        }
        i = 1;
        while i <= 500 {
            if cnt[i] % 2 != 0 {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
