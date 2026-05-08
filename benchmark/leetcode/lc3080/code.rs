impl Solution {
    pub fn unmarked_sum_array(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> Vec<i64> {
        let n = nums.len();

        let mut marked: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            marked.push(false);
            i = i + 1;
        }

        let mut result: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let idx_i32 = queries[q][0];
            let k = queries[q][1];
            let idx = idx_i32 as usize;

            if !marked[idx] {
                marked[idx] = true;
            }

            let mut t: i32 = 0;
            while t < k {
                let mut best: usize = n;
                let mut j: usize = 0;
                while j < n {
                    if !marked[j] {
                        if best == n {
                            best = j;
                        } else if nums[j] < nums[best] || (nums[j] == nums[best] && j < best) {
                            best = j;
                        }
                    }
                    j = j + 1;
                }
                if best < n {
                    marked[best] = true;
                }
                t = t + 1;
            }

            let mut unmarked_sum: i128 = 0;
            let mut p: usize = 0;
            while p < n {
                if !marked[p] {
                    unmarked_sum = unmarked_sum + nums[p] as i128;
                }
                p = p + 1;
            }

            result.push(unmarked_sum as i64);
            q = q + 1;
        }

        result
    }
}
