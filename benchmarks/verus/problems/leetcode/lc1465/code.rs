impl Solution {
    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> Vec<i32> {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
        {
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                i = i + 1;
            } else {
                result.push(b[j]);
                j = j + 1;
            }
        }
        result
    }

    fn ms_sort(input: &Vec<i32>) -> Vec<i32> {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
        {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
        {
            right.push(input[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        result
    }

    fn find_max_gap(cuts: &Vec<i32>, bound: i32) -> i32 {
        let sorted = Self::ms_sort(cuts);
        let n = sorted.len();
        let mut max_g: i32 = sorted[0];
        let mut i: usize = 1;
        while i < n
        {
            let gap = sorted[i] - sorted[i - 1];
            if gap > max_g {
                max_g = gap;
            }
            i = i + 1;
        }
        let last_gap = bound - sorted[n - 1];
        if last_gap > max_g {
            max_g = last_gap;
        }
        max_g
    }

    pub fn max_area(h: i32, w: i32, horizontal_cuts: Vec<i32>, vertical_cuts: Vec<i32>) -> i32 {
        let max_h = Self::find_max_gap(&horizontal_cuts, h);
        let max_v = Self::find_max_gap(&vertical_cuts, w);
        ((max_h as i64 * max_v as i64) % 1_000_000_007i64) as i32
    }
}
