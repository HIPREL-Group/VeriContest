impl Solution {
    pub const MOD: i64 = 1_000_000_007;

    pub fn number_of_good_partitions(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut last_map: std::collections::HashMap<i32, usize> = std::collections::HashMap::new();
        let mut idx: usize = 0;
        while idx < n {
            let v = nums[idx];
            last_map.insert(v, idx);
            idx += 1;
        }

        let mut answer: i64 = 1;
        let mut start = 0usize;

        while start < n {
            let old_start = start;
            let mut end = *last_map.get(&nums[start]).unwrap();
            let mut i = start + 1;
            while i < n && i <= end {
                let old_end = end;
                let candidate = *last_map.get(&nums[i]).unwrap();
                if candidate > end {
                    end = candidate;
                }
                i += 1;
            }
            start = end + 1;
            if start < n {
                answer = (answer * 2) % Self::MOD;
            }
        }

        answer as i32
    }
}
