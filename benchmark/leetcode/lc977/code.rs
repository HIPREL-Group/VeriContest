impl Solution {
    pub fn sorted_squares(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut result: Vec<i32> = Vec::with_capacity(n);

        let mut init_k: usize = 0;
        while init_k < n {
            result.push(0i32);
            init_k = init_k + 1;
        }

        let mut k: usize = 0;
        let mut left: usize = 0;

        while k < n {
            let right: usize = n - 1 - k + left;
            let pos: usize = n - 1 - k;

            let left_sq: i32 = nums[left] * nums[left];
            let right_sq: i32 = nums[right] * nums[right];

            if left_sq > right_sq {
                result[pos] = left_sq;
                left = left + 1;
            } else {
                result[pos] = right_sq;
            }

            k = k + 1;
        }

        result
    }
}
