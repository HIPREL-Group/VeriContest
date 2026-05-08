impl Solution {
    pub fn minimum_sum(nums: Vec<i32>) -> i32 {
        let n = nums.len();

        let mut left_idx: Vec<usize> = Vec::new();
        left_idx.push(0);

        let mut p: usize = 1;
        while p < n {
            let mut best = left_idx[p - 1];
            if nums[p] < nums[best] {
                best = p;
            }
            left_idx.push(best);
            p += 1;
        }

        let mut right_idx: Vec<usize> = Vec::new();
        let mut q: usize = 0;
        while q < n {
            right_idx.push(q);
            q += 1;
        }

        let mut q: usize = n - 1;
        while q > 0 {
            let prev = q - 1;
            let mut best = right_idx[q];
            if nums[prev] <= nums[best] {
                best = prev;
            }
            right_idx[prev] = best;
            q -= 1;
        }

        let mut best_sum: i32 = 300000001;
        let mut j: usize = 1;
        while j + 1 < n {
            let left = left_idx[j - 1];
            let right = right_idx[j + 1];
            if nums[left] < nums[j] && nums[right] < nums[j] {
                let candidate = nums[left] + nums[j] + nums[right];
                if candidate < best_sum {
                    best_sum = candidate;
                }
            }
            j += 1;
        }

        if best_sum == 300000001 {
            -1
        } else {
            best_sum
        }
    }
}
