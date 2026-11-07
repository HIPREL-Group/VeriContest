impl Solution {
    fn is_non_decreasing_vec(arr: &Vec<i32>) -> bool {
        if arr.len() <= 1 {
            return true;
        }
        let mut i: usize = 1;
        while i < arr.len() {
            if arr[i - 1] > arr[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    pub fn minimum_pair_removal(nums: Vec<i32>) -> i32 {
        let mut arr = nums;
        let mut ops: usize = 0;
        let mut sorted = Self::is_non_decreasing_vec(&arr);

        while !sorted {
            let n = arr.len();
            let mut best_idx: usize = 0;
            let mut best_sum: i64 = arr[0] as i64 + arr[1] as i64;
            let mut i: usize = 1;
            while i < n - 1 {
                let cur_sum: i64 = arr[i] as i64 + arr[i + 1] as i64;
                if cur_sum < best_sum {
                    best_idx = i;
                    best_sum = cur_sum;
                }
                i += 1;
            }

            let mut next_arr: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < best_idx {
                next_arr.push(arr[j]);
                j += 1;
            }
            let merged = (arr[best_idx] as i64 + arr[best_idx + 1] as i64) as i32;
            next_arr.push(merged);
            j = best_idx + 2;
            while j < n {
                next_arr.push(arr[j]);
                j += 1;
            }

            arr = next_arr;
            ops += 1;
            sorted = Self::is_non_decreasing_vec(&arr);
        }

        ops as i32
    }
}
