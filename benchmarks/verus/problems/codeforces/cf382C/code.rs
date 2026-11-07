impl Solution {
    pub fn arithmetic_progression_insertions(nums: Vec<i64>) -> Option<Vec<i64>> {
        let n = nums.len();
        if n == 1 {
            return None;
        }
        if n == 2 {
            let a = nums[0];
            let b = nums[1];
            let d = b - a;
            if d == 0 {
                let mut ans = Vec::new();
                ans.push(a);
                let out = Some(ans);
                return out;
            }
            if d % 2 == 0 {
                let mut ans = Vec::new();
                ans.push(a - d);
                ans.push(a + d / 2);
                ans.push(b + d);
                let out = Some(ans);
                return out;
            }
            let mut ans = Vec::new();
            ans.push(a - d);
            ans.push(b + d);
            let out = Some(ans);
            return out;
        }

        let mut min_diff = nums[1] - nums[0];
        let mut i = 1usize;
        while i + 1 < n {
            let cur = nums[i + 1] - nums[i];
            if cur < min_diff {
                min_diff = cur;
            }
            i += 1;
        }

        let mut has_double = false;
        let mut double_idx = 0usize;
        let mut j = 0usize;
        while j + 1 < n {
            let cur = nums[j + 1] - nums[j];
            if cur == min_diff {
                j += 1;
                continue;
            }
            if cur == 2 * min_diff && !has_double {
                has_double = true;
                double_idx = j;
                j += 1;
                continue;
            }
            let ans = Vec::new();
            return Some(ans);
        }

        if min_diff == 0 {
            let mut ans = Vec::new();
            ans.push(nums[0]);
            let out = Some(ans);
            return out;
        }
        if has_double {
            let mut ans = Vec::new();
            ans.push(nums[double_idx] + min_diff);
            let out = Some(ans);
            return out;
        }
        let mut ans = Vec::new();
        ans.push(nums[0] - min_diff);
        ans.push(nums[n - 1] + min_diff);
        let out = Some(ans);
        out
    }
}
