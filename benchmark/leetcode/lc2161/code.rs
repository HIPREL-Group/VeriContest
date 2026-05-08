impl Solution {
    pub fn pivot_array(nums: Vec<i32>, pivot: i32) -> Vec<i32> {
        let n = nums.len();
        let mut less: Vec<i32> = Vec::new();
        let mut equal: Vec<i32> = Vec::new();
        let mut greater: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if nums[i] < pivot {
                less.push(nums[i]);
            } else if nums[i] == pivot {
                equal.push(nums[i]);
            } else {
                greater.push(nums[i]);
            }
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < less.len() {
            result.push(less[j]);
            j = j + 1;
        }
        let mut k: usize = 0;
        while k < equal.len() {
            let v = equal[k];
            result.push(v);
            k = k + 1;
        }
        let mut t: usize = 0;
        while t < greater.len() {
            let v = greater[t];
            result.push(v);
            t = t + 1;
        }
        result
    }
}
