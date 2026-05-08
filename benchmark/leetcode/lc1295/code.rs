impl Solution {
    pub fn find_numbers(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let x = nums[i];
            if (x >= 10 && x <= 99) || (x >= 1000 && x <= 9999) || x == 100000 {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}
