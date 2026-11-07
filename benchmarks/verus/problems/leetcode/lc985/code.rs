impl Solution {
    pub fn sum_even_after_queries(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> Vec<i32> {
        let mut nums = nums;
        let mut even_sum: i128 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            if nums[i] % 2 == 0 {
                even_sum = even_sum + nums[i] as i128;
            }
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let val = queries[q][0];
            let idx = queries[q][1] as usize;

            let old = nums[idx];
            let new_val_i64 = old as i64 + val as i64;
            let new_val = new_val_i64 as i32;
            nums[idx] = new_val;

            even_sum = 0;
            let mut p: usize = 0;
            while p < nums.len() {
                if nums[p] % 2 == 0 {
                    even_sum = even_sum + nums[p] as i128;
                }
                p = p + 1;
            }

            result.push(even_sum as i32);
            q = q + 1;
        }

        result
    }
}
