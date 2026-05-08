impl Solution {
    pub fn find_missing_elements(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut min_v = nums[0];
        let mut max_v = nums[0];
        let mut i: usize = 1;

        while i < n {
            if nums[i] < min_v {
                min_v = nums[i];
            }
            if nums[i] > max_v {
                max_v = nums[i];
            }
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut k = min_v + 1;

        while k < max_v {
            let mut found = false;
            let mut j: usize = 0;

            while j < n {
                if nums[j] == k {
                    found = true;
                }
                j = j + 1;
            }

            if !found {
                result.push(k);
            }

            k = k + 1;
        }

        result
    }
}
