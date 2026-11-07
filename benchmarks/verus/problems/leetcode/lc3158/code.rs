impl Solution {
    pub fn duplicate_numbers_xor(nums: Vec<i32>) -> i32 {
        let mut freq: Vec<i32> = vec![0i32; 51];
        let mut i: usize = 0;
        while i < nums.len() {
            let idx: usize = nums[i] as usize;
            if freq[idx] <= 1 {
                freq[idx] = freq[idx] + 1;
            }
            i = i + 1;
        }

        let mut ans: i32 = 0;
        let mut v: usize = 1;
        while v <= 50 {
            if freq[v] == 2 {
                ans = ans ^ v as i32;
            }
            v = v + 1;
        }
        ans
    }
}
