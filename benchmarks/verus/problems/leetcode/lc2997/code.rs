impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 {
        let mut total_xor: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            total_xor = total_xor ^ nums[i];
            i = i + 1;
        }

        let mut diff: i32 = total_xor ^ k;
        let mut answer: i32 = 0;

        while diff > 0 {
            if diff % 2 == 1 {
                answer = answer + 1;
            }
            diff = diff / 2;
        }

        answer
    }
}
