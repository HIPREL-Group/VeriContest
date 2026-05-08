impl Solution {
    fn contains_in_suffix(nums: &Vec<i32>, ops: usize, v: i32) -> bool {
        let n = nums.len();
        let mut t: usize = 0;
        while t < ops {
            let idx = n - ops + t;
            if nums[idx] == v {
                return true;
            }
            t = t + 1;
        }
        false
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut ops: usize = 1;
        while ops <= n {
            let mut ok = true;
            let mut v: i32 = 1;
            while v <= k {
                let found = Self::contains_in_suffix(&nums, ops, v);
                if !found {
                    ok = false;
                }
                v = v + 1;
            }
            if ok {
                return ops as i32;
            }
            ops = ops + 1;
        }
        n as i32
    }
}
