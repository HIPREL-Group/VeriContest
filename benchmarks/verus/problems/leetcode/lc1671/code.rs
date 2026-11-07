impl Solution {
    pub fn minimum_mountain_removals(nums: Vec<i32>) -> i32 {
        let n = nums.len();

        let mut lis: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n {
            lis.push(1i32);
            idx = idx + 1;
        }

        let mut i: usize = 1;
        while i < n {
            let mut j: usize = 0;
            while j < i {
                if nums[j] < nums[i] {
                    if lis[j] + 1 > lis[i] {
                        lis[i] = lis[j] + 1;
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }

        let mut lds: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n {
            lds.push(1i32);
            idx = idx + 1;
        }

        let mut k: usize = 1;
        while k < n {
            let i_idx: usize = n - 1 - k;
            let mut j: usize = i_idx + 1;
            while j < n {
                if nums[j] < nums[i_idx] {
                    if lds[j] + 1 > lds[i_idx] {
                        lds[i_idx] = lds[j] + 1;
                    }
                }
                j = j + 1;
            }
            k = k + 1;
        }

        let mut result: i32 = n as i32;
        let mut i2: usize = 0;
        while i2 < n {
            if lis[i2] > 1 && lds[i2] > 1 {
                let mountain_len: i32 = lis[i2] + lds[i2] - 1;
                let removals: i32 = n as i32 - mountain_len;
                if removals < result {
                    result = removals;
                }
            }
            i2 = i2 + 1;
        }

        result
    }
}
