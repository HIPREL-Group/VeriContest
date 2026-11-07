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

    fn ms_sort(nums: &Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(nums[0]);
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
        {
            left.push(nums[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
        {
            right.push(nums[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        result
    }

    pub fn max_width_of_vertical_area(points: Vec<Vec<i32>>) -> i32 {
        let n = points.len();
        let mut xs: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
        {
            xs.push(points[i][0]);
            i = i + 1;
        }
        let sorted = Self::ms_sort(&xs);
        let mut max_gap: i32 = 0;
        let mut k: usize = 1;
        while k < sorted.len()
        {
            let gap = sorted[k] - sorted[k - 1];
            if gap > max_gap {
                max_gap = gap;
            }
            k = k + 1;
        }
        max_gap
    }
}
