impl Solution {
    pub fn find_k_distant_indices(nums: Vec<i32>, key: i32, k: i32) -> Vec<i32> {
        let n = nums.len();
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            let mut found: bool = false;
            while j < n {
                let diff: usize = if i >= j { i - j } else { j - i };
                if nums[j] == key && diff <= k as usize {
                    found = true;
                }
                j = j + 1;
            }
            if found {
                result.push(i as i32);
            }
            i = i + 1;
        }
        result
    }
}
