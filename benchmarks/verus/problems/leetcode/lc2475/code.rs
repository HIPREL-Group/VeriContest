impl Solution {
    pub fn unequal_triplets(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        if n < 3 {
            return 0;
        }
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n - 2 {
            let mut j: usize = i + 1;
            while j < n - 1 {
                let mut k: usize = j + 1;
                while k < n {
                    if nums[i] != nums[j] && nums[i] != nums[k] && nums[j] != nums[k] {
                        ans = ans + 1;
                    }
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        ans
    }
}
