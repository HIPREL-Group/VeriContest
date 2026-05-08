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

    pub fn min_difference(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        if n <= 4 { return 0; }

        let nums = Self::ms_sort(&nums);

        let d1 = nums[n - 1] - nums[3];
        let d2 = nums[n - 2] - nums[2];
        let d3 = nums[n - 3] - nums[1];
        let d4 = nums[n - 4] - nums[0];
        let mut result = d1;
        if d2 < result {
            result = d2;
        }
        if d3 < result {
            result = d3;
        }
        if d4 < result {
            result = d4;
        }
        result
    }
}