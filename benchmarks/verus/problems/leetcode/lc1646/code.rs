impl Solution {
    pub fn get_maximum_generated(n: i32) -> i32 {
        if n == 0 {
            return 0;
        }
        if n == 1 {
            return 1;
        }
        let n_usize = n as usize;
        let mut nums: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx <= n_usize {
            nums.push(0i32);
            idx += 1;
        }
        nums[0] = 0i32;
        nums[1] = 1i32;
        let mut max_val: i32 = 1;
        let mut i: usize = 2;
        while i <= n_usize {
            let half = i / 2;
            if i % 2 == 0 {
                let val = nums[half];
                nums[i] = val;
            } else {
                let val = nums[half] + nums[half + 1];
                nums[i] = val;
            }
            if nums[i] > max_val {
                max_val = nums[i];
            }
            i += 1;
        }
        max_val
    }
}
