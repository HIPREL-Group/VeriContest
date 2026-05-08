impl Solution {
    pub fn is_ideal_permutation(nums: Vec<i32>) -> bool {
        let n = nums.len();
        if n <= 2 {
            return true;
        }

        let mut cmax = nums[0];
        let mut j: usize = 2;
        while j < n {
            if cmax > nums[j] {
                return false;
            }
            let prev = nums[j - 1];
            if prev > cmax {
                cmax = prev;
            }
            j += 1;
        }

        true
    }
}
