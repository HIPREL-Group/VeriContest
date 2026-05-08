impl Solution {
    pub fn find_missing_ranges(nums: Vec<i32>, lower: i32, upper: i32) -> Vec<Vec<i32>> {
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut next = lower;
        let mut i: usize = 0;

        while i < nums.len() {
            let current = nums[i];
            let next_after = if current == i32::MAX { i32::MAX } else { current + 1 };
            if next < current {
                result.push(vec![next, current - 1]);
            }
            next = next_after;
            i += 1;
        }

        if next <= upper {
            result.push(vec![next, upper]);
        }

        result
    }
}
