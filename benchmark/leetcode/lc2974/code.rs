impl Solution {
    fn count_value_exec(nums: &Vec<i32>, value: i32) -> i32 {
        let n = nums.len();
        let mut i: usize = 0;
        let mut c: i32 = 0;
        while i < n {
            if nums[i] == value {
                c = c + 1;
            }
            i = i + 1;
        }
        c
    }

    pub fn number_game(nums: Vec<i32>) -> Vec<i32> {
        let mut result: Vec<i32> = Vec::new();
        let mut has_pending = false;
        let mut pending: i32 = 0;
        let mut value: i32 = 1;
        while value <= 100 {
            let cnt = Self::count_value_exec(&nums, value);
            let mut t: i32 = 0;
            while t < cnt {
                if has_pending {
                    result.push(value);
                    result.push(pending);
                    has_pending = false;
                } else {
                    pending = value;
                    has_pending = true;
                }
                t = t + 1;
            }
            value = value + 1;
        }
        result
    }
}
