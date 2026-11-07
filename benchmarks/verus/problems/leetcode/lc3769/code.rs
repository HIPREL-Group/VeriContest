impl Solution {
    fn reflection_with_acc(cur: i64, acc: i64) -> i64 {
        if cur == 0 {
            acc
        } else {
            let bit = cur % 2;
            if acc > i64::MAX / 2 {
                0
            } else {
                let doubled = acc * 2;
                if doubled > i64::MAX - bit {
                    0
                } else {
                    Solution::reflection_with_acc(cur / 2, doubled + bit)
                }
            }
        }
    }

    fn reflection_value(x: i32) -> i64 {
        Solution::reflection_with_acc(x as i64, 0)
    }

    fn reflection_rank_value(x: i32) -> i64 {
        let r = Solution::reflection_value(x);
        if r > i64::MAX / 1_000_000_001 {
            0
        } else {
            let prod = r * 1_000_000_001i64;
            if prod > i64::MAX - x as i64 {
                0
            } else {
                prod + x as i64
            }
        }
    }

    pub fn sort_by_reflection(nums: Vec<i32>) -> Vec<i32> {
        let mut nums = nums;
        let n = nums.len();
        if n == 0 {
            return nums;
        }
        let mut i: usize = 1;
        while i < n {
            let mut j: usize = i;
            while j != 0 {
                let left = nums[j - 1];
                let right = nums[j];
                let left_rank = Solution::reflection_rank_value(left);
                let right_rank = Solution::reflection_rank_value(right);
                if left_rank > right_rank {
                    let tmp_left = nums[j - 1];
                    let tmp_right = nums[j];
                    nums[j - 1] = tmp_right;
                    nums[j] = tmp_left;
                }
                j = j - 1;
            }
            i = i + 1;
        }
        nums
    }
}
