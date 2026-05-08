impl Solution {
    pub fn num_subarray_product_less_than_k(nums: Vec<i32>, k: i32) -> i32 {
        if k <= 1 {
            return 0;
        }
        let n = nums.len();
        let mut count: i32 = 0;
        let mut prod: u64 = 1;
        let mut left: usize = 0;
        let mut right: usize = 0;
        while right < n {
            prod = prod * (nums[right] as u64);
            while left <= right && prod >= k as u64 {
                prod = prod / (nums[left] as u64);
                left = left + 1;
            }
            count = count + ((right + 1 - left) as i32);
            right = right + 1;
        }
        count
    }
}
