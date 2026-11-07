impl Solution {
    pub fn construct_transformed_array(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut result = vec![0i32; n];
        let mut i: usize = 0;
        while i < n {
            let delta: i32 = nums[i];
            if delta == 0 {
                result[i] = nums[i];
            } else if delta > 0 {
                let mut pos: usize = i;
                let mut step: i32 = 0;
                while step < delta {
                    if pos + 1 < n {
                        pos = pos + 1;
                    } else {
                        pos = 0;
                    }
                    step = step + 1;
                }
                result[i] = nums[pos];
            } else {
                let mut pos: usize = i;
                let mut step: i32 = 0;
                let target: i32 = -delta;
                while step < target {
                    if pos > 0 {
                        pos = pos - 1;
                    } else {
                        pos = n - 1;
                    }
                    step = step + 1;
                }
                result[i] = nums[pos];
            }
            i = i + 1;
        }
        result
    }
}
