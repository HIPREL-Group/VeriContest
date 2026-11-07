impl Solution {
    pub fn min_changes(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let pairs = n / 2;
        let ku = k as usize;
        let mut change_count = vec![0i32; ku + 2];
        change_count[0] = pairs as i32;

        let mut i = 0usize;
        while i < pairs {
            let left = nums[i];
            let right = nums[n - 1 - i];
            let cur_diff_i32 = if left >= right {
                left.checked_sub(right).unwrap_or(0)
            } else {
                right.checked_sub(left).unwrap_or(0)
            };
            let cur_diff = cur_diff_i32 as usize;

            let a = if left >= right { left } else { right };
            let b1 = k.checked_sub(left).unwrap_or(0);
            let b2 = k.checked_sub(right).unwrap_or(0);
            let b = if b1 >= b2 { b1 } else { b2 };
            let max_diff_i32 = if a >= b { a } else { b };
            let max_diff = max_diff_i32 as usize;

            if cur_diff <= ku {
                change_count[cur_diff] = change_count[cur_diff].checked_sub(1).unwrap_or(change_count[cur_diff]);
                change_count[cur_diff + 1] = change_count[cur_diff + 1].checked_add(1).unwrap_or(change_count[cur_diff + 1]);
            }
            if max_diff <= ku {
                change_count[max_diff + 1] = change_count[max_diff + 1].checked_add(1).unwrap_or(change_count[max_diff + 1]);
            }

            i += 1;
        }

        let mut cur_changes = 0i32;
        let mut min_changes = pairs as i32;
        let mut d = 0usize;
        while d <= ku {
            cur_changes = cur_changes.checked_add(change_count[d]).unwrap_or(cur_changes);
            if cur_changes < min_changes {
                min_changes = cur_changes;
            }
            d += 1;
        }

        if min_changes < 0 { 0 } else { min_changes }
    }
}
