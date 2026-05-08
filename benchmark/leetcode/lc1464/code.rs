impl Solution {
    pub fn max_product(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut best: i32;

        best = (nums[0] - 1) * (nums[1] - 1);

        let mut i: usize = 0;
        while i < n {
            let mut j: usize = i + 1;
            while j < n {
                let prod = (nums[i] - 1) * (nums[j] - 1);
                if prod > best {
                    best = prod;
                }
                j += 1;
            }
            i += 1;
        }
        best
    }
}
