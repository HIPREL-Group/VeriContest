impl Solution {
    pub fn minimum_abs_difference(arr: Vec<i32>) -> Vec<Vec<i32>> {
        let n = arr.len();
        let mut sorted = arr;

        let mut i: usize = 1;
        while i < n {
            let key = sorted[i];
            let mut j = i;
            while j > 0 && sorted[j - 1] > key {
                sorted[j] = sorted[j - 1];
                j = j - 1;
            }
            sorted[j] = key;
            i = i + 1;
        }

        let mut min_diff: i32 = sorted[1] - sorted[0];
        let mut i: usize = 2;
        while i < n {
            let diff = sorted[i] - sorted[i - 1];
            if diff < min_diff {
                min_diff = diff;
            }
            i = i + 1;
        }

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 1;
        while i < n {
            if sorted[i] - sorted[i - 1] == min_diff {
                let pair: Vec<i32> = vec![sorted[i - 1], sorted[i]];
                result.push(pair);
            }
            i = i + 1;
        }

        result
    }
}
