impl Solution {
    pub fn height_checker(heights: Vec<i32>) -> i32 {
        let n = heights.len();
        let mut expected: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n {
            expected.push(heights[idx]);
            idx += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let mut min_idx: usize = i;
            let mut j: usize = i + 1;
            while j < n {
                if expected[j] < expected[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            let temp_i = expected[i];
            let temp_min = expected[min_idx];
            expected[i] = temp_min;
            expected[min_idx] = temp_i;
            i += 1;
        }

        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if heights[i] != expected[i] {
                count += 1;
            }
            i += 1;
        }

        count
    }
}
