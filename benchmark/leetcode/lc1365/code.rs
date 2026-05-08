impl Solution {
    pub fn smaller_numbers_than_current(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut freq: Vec<i32> = Vec::new();
        let mut v: usize = 0;
        while v <= 100 {
            freq.push(0);
            v = v + 1;
        }
        let mut i: usize = 0;
        while i < n {
            let val = nums[i] as usize;
            freq[val] = freq[val] + 1;
            i = i + 1;
        }
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut v: usize = 1;
        while v <= 100 {
            prefix.push(prefix[v - 1] + freq[v - 1]);
            v = v + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            result.push(prefix[nums[i] as usize]);
            i = i + 1;
        }
        result
    }
}
