impl Solution {
    pub fn find_disappeared_numbers(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        
        let mut seen: Vec<bool> = Vec::new();
        let mut idx: usize = 0;
        
        while idx < n + 1 {
            seen.push(false);
            idx += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = nums[i] as usize;
            seen[val] = true;
            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 1;

        while k <= n {
            if !seen[k] {
                result.push(k as i32);
            }
            k += 1;
        }

        result
    }
}
