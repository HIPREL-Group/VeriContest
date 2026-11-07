impl Solution {
    pub fn max_distance(arrays: Vec<Vec<i32>>) -> i32
    {
        let mut min_val = arrays[0][0];
        let mut max_val = arrays[0][arrays[0].len() - 1];
        let mut result = 0i32;
        let mut i: usize = 1;
        while i < arrays.len()
        {
            let curr_len = arrays[i].len();
            let curr_last = curr_len - 1;
            let curr_min = arrays[i][0];
            let curr_max = arrays[i][curr_last];
            let old_min_val = min_val;
            let old_max_val = max_val;
            let old_result = result;

            let mut candidate = curr_max - old_min_val;
            let other = old_max_val - curr_min;
            if other > candidate {
                candidate = other;
            }
            if i == 1 || candidate > result {
                result = candidate;
            }

            if curr_min < min_val {
                min_val = curr_min;
            }
            if curr_max > max_val {
                max_val = curr_max;
            }

            i += 1;
        }
        result
    }
}
