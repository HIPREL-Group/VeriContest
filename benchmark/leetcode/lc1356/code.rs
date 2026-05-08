impl Solution {
    fn count_ones(n: i32) -> i32 {
        let mut count: i32 = 0;
        let mut val: i32 = n;
        while val > 0 {
            count = count + (val % 2);
            val = val / 2;
        }
        count
    }

    pub fn sort_by_bits(arr: Vec<i32>) -> Vec<i32> {
        let mut result = arr;
        let n = result.len();
        let mut i: usize = 0;
        while i < n {
            let mut min_idx: usize = i;
            let mut j: usize = i + 1;
            while j < n {
                let ones_j = Self::count_ones(result[j]);
                let ones_min = Self::count_ones(result[min_idx]);
                if ones_j < ones_min || (ones_j == ones_min && result[j] < result[min_idx]) {
                    min_idx = j;
                }
                j = j + 1;
            }
            let temp = result[i];
            let val_at_min = result[min_idx];
            result[i] = val_at_min;
            result[min_idx] = temp;
            i = i + 1;
        }
        result
    }
}
