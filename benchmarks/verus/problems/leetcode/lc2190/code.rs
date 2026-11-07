impl Solution {
    pub fn most_frequent(nums: Vec<i32>, key: i32) -> i32 {
        let n: usize = nums.len();
        let mut best_target: i32 = 1;
        let mut best_count: usize = 0;

        let mut cnt0: usize = 0;
        let mut j0: usize = 1;
        while j0 < n {
            if nums[j0 - 1] == key && nums[j0] == 1 {
                cnt0 = cnt0 + 1;
            }
            j0 = j0 + 1;
        }
        best_count = cnt0;

        let mut target: i32 = 2;
        while target <= 1000 {
            let mut cnt: usize = 0;
            let mut j: usize = 1;
            while j < n {
                if nums[j - 1] == key && nums[j] == target {
                    cnt = cnt + 1;
                }
                j = j + 1;
            }

            let prev_best_count: usize = best_count;
            let prev_best_target: i32 = best_target;
            if cnt > best_count {
                best_count = cnt;
                best_target = target;
            }
            target = target + 1;
        }

        best_target
    }
}
