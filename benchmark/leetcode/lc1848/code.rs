impl Solution {
    pub fn get_min_distance(nums: Vec<i32>, target: i32, start: i32) -> i32 {
        let n: usize = nums.len();
        let mut min_dist: i32 = n as i32;
        let mut i: usize = 0;
        
        while i < n {
            if nums[i] == target {
                let dist = if (i as i32) > start {
                    (i as i32) - start
                } else {
                    start - (i as i32)
                };
                if dist < min_dist {
                    min_dist = dist;
                }
            }
            i = i + 1;
        }
        
        min_dist
    }
}
