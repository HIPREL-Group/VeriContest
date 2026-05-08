impl Solution {
    fn solve_k(nums: &Vec<i32>, i: usize, j: usize, k: usize, acc: i64) -> i64 {
        if k >= nums.len() {
            acc
        } else {
            let v: i64 = (nums[i] as i64 - nums[j] as i64) * nums[k] as i64;
            let acc2: i64 = if acc >= v { acc } else { v };
            Self::solve_k(nums, i, j, k + 1, acc2)
        }
    }

    fn solve_j(nums: &Vec<i32>, i: usize, j: usize, acc: i64) -> i64 {
        if j >= nums.len() {
            acc
        } else {
            let acc2: i64 = Self::solve_k(nums, i, j, j + 1, acc);
            Self::solve_j(nums, i, j + 1, acc2)
        }
    }

    fn solve_i(nums: &Vec<i32>, i: usize, acc: i64) -> i64 {
        if i >= nums.len() {
            acc
        } else {
            let acc2: i64 = Self::solve_j(nums, i, i + 1, acc);
            Self::solve_i(nums, i + 1, acc2)
        }
    }

    pub fn maximum_triplet_value(nums: Vec<i32>) -> i64 {
        Self::solve_i(&nums, 0, 0)
    }
}
