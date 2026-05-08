impl Solution {
    fn count_value_exec(nums: &Vec<i32>, target: i32, idx: usize) -> usize {
        if idx >= nums.len() {
            0
        } else {
            let tail: usize = Self::count_value_exec(nums, target, idx + 1);
            let add: usize = if nums[idx] == target { 1 } else { 0 };
            tail + add
        }
    }

    fn check_single_exec(nums: &Vec<i32>, v: usize, n: usize) -> bool {
        if v >= n {
            true
        } else {
            let cnt: usize = Self::count_value_exec(nums, v as i32, 0);
            cnt == 1 && Self::check_single_exec(nums, v + 1, n)
        }
    }

    pub fn is_good(nums: Vec<i32>) -> bool {
        if nums.len() < 2 {
            return false;
        }

        let n: usize = nums.len() - 1;
        let cnt_n: usize = Self::count_value_exec(&nums, n as i32, 0);
        let ok_single: bool = Self::check_single_exec(&nums, 1, n);
        cnt_n == 2 && ok_single
    }
}
