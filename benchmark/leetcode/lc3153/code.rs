impl Solution {
    fn digit_diff_count_exec(a: i32, b: i32, pos: usize) -> i64 {
        if pos == 0 {
            0
        } else {
            let next = Self::digit_diff_count_exec(a / 10, b / 10, pos - 1);
            let add = if a % 10 != b % 10 { 1i64 } else { 0i64 };
            next + add
        }
    }

    fn pair_sum_for_i_exec(nums: &Vec<i32>, i: usize, j: usize) -> i64 {
        if j == 0 {
            0
        } else {
            let prev = Self::pair_sum_for_i_exec(nums, i, j - 1);
            let diff = Self::digit_diff_count_exec(nums[i], nums[j - 1], 9);
            prev + diff
        }
    }

    fn all_pair_sum_exec(nums: &Vec<i32>, end: usize) -> i64 {
        if end == 0 {
            0
        } else {
            let prev = Self::all_pair_sum_exec(nums, end - 1);
            let add = Self::pair_sum_for_i_exec(nums, end - 1, end - 1);
            prev + add
        }
    }

    pub fn sum_digit_differences(nums: Vec<i32>) -> i64 {
        Self::all_pair_sum_exec(&nums, nums.len())
    }
}
