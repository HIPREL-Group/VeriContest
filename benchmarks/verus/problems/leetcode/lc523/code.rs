use std::collections::HashMap;

impl Solution {
    pub fn check_subarray_sum(nums: Vec<i32>, k: i32) -> bool {
        let mut map: HashMap<i32, usize> = HashMap::new();
        map.insert(0, 0);
        
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        
        while i < nums.len() {
            sum = sum + nums[i] as i64;
            let r = (sum % (k as i64)) as i32;
            
            if let Some(prev) = map.get(&r) {
                if i + 1 - *prev >= 2 {
                    return true;
                }
            } else {
                map.insert(r, i + 1);
            }
            
            i = i + 1;
        }
        
        false
    }
}
