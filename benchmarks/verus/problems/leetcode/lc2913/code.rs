impl Solution {
    fn contains_range(nums: &Vec<i32>, start: usize, end: usize, value: i32) -> bool {
        let mut k: usize = start;
        let mut found = false;
        while k < end {
            if nums[k] == value {
                found = true;
            }
            k = k + 1;
        }
        found
    }

    fn distinct_count_range(nums: &Vec<i32>, start: usize, end: usize) -> i32 {
        let mut value: i32 = 1;
        let mut count: i32 = 0;
        while value <= 100 {
            if Self::contains_range(nums, start, end, value) {
                count = count + 1;
            }
            value = value + 1;
        }
        count
    }

    pub fn sum_counts(nums: Vec<i32>) -> i32 {
        let n: usize = nums.len();
        let mut i: usize = 0;
        let mut total: i32 = 0;
        while i < n {
            let mut end: usize = i + 1;
            let mut row_sum: i32 = 0;
            while end <= n {
                let d = Self::distinct_count_range(&nums, i, end);
                row_sum = row_sum + d * d;
                end = end + 1;
            }
            total = total + row_sum;
            i = i + 1;
        }
        total
    }
}
