impl Solution {
    pub fn find_error_nums(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut dup: i32 = 1;
        let mut miss: i32 = 1;
        let mut found_dup: bool = false;
        let mut found_miss: bool = false;
        let mut k: usize = 1;
        while k <= n {
            let mut seen_first: bool = false;
            let mut seen_second: bool = false;
            let mut i: usize = 0;
            while i < n {
                if nums[i] == k as i32 {
                    if seen_first {
                        seen_second = true;
                    }
                    seen_first = true;
                }
                i = i + 1;
            }
            if seen_second && !found_dup {
                dup = k as i32;
                found_dup = true;
            }
            if !seen_first && !found_miss {
                miss = k as i32;
                found_miss = true;
            }
            k = k + 1;
        }
        let mut result = Vec::new();
        result.push(dup);
        result.push(miss);
        result
    }
}
