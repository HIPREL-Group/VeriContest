impl Solution {
    pub fn transform_array(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut even_count: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if (nums[i] as u32) % 2 == 0 {
                even_count += 1;
            }
            i += 1;
        }
        let mut answer: Vec<i32> = vec![0i32; n];
        let mut j: usize = even_count;
        while j < n {
            answer[j] = 1;
            j += 1;
        }
        answer
    }
}
