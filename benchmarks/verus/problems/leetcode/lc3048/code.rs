impl Solution {
    fn can_mark(nums: &Vec<i32>, change_indices: &Vec<i32>, t: usize) -> bool
    {
        let n = nums.len();
        let mut last: Vec<i32> = vec![-1; n];

        let mut i: usize = 0;
        while i < t
        {
            let idx = (change_indices[i] - 1) as usize;
            last[idx] = i as i32;
            i += 1;
        }

        i = 0;
        while i < n
        {
            let cur = last[i];
            if cur == -1 {
                return false;
            }
            i += 1;
        }

        let mut slots: i64 = 0;
        i = 0;
        while i < t
        {
            let idx = (change_indices[i] - 1) as usize;
            if last[idx] == i as i32 {
                let old_slots = slots;
                if old_slots < nums[idx] as i64 {
                    return false;
                }
                slots -= nums[idx] as i64;
            } else {
                let old_slots = slots;
                slots += 1;
            }
            i += 1;
        }

        true
    }

    pub fn earliest_second_to_mark_indices(nums: Vec<i32>, change_indices: Vec<i32>) -> i32
    {
        let m = change_indices.len();
        let mut t: usize = 1;
        while t <= m
        {
            if Self::can_mark(&nums, &change_indices, t) {
                return t as i32;
            }
            t += 1;
        }
        -1
    }
}
