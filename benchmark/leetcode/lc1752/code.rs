impl Solution {
    pub fn check(nums: Vec<i32>) -> bool {
        let n = nums.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let next: usize = if i + 1 < n { i + 1 } else { 0 };
            if nums[i] > nums[next] {
                count = count + 1;
            }
            i = i + 1;
        }
        count <= 1
    }
}
