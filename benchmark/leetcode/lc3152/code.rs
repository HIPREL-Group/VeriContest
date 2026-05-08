impl Solution {
    pub fn is_array_special(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> Vec<bool> {
        let n = nums.len();
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);

        let mut i: usize = 1;
        while i < n {
            let mut next = prefix[i - 1];
            let prev_val = nums[i - 1];
            let curr_val = nums[i];
            if prev_val % 2 == curr_val % 2 {
                next = next + 1;
            }
            prefix.push(next);
            i = i + 1;
        }

        let mut answer: Vec<bool> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let left_i = queries[q][0];
            let right_i = queries[q][1];
            let left = left_i as usize;
            let right = right_i as usize;
            let is_special = prefix[left] == prefix[right];
            answer.push(is_special);
            q = q + 1;
        }

        answer
    }
}