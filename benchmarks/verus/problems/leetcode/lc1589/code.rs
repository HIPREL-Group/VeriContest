impl Solution {
    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> Vec<i32> {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len() {
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
        while i < mid {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n {
            right.push(input[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        result
    }

    fn ms_merge_i64(a: &Vec<i64>, b: &Vec<i64>) -> Vec<i64> {
        let mut result: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len() {
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

    fn ms_sort_i64(input: &Vec<i64>) -> Vec<i64> {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i64> = Vec::new();
        let mut j: usize = mid;
        while j < n {
            right.push(input[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort_i64(&left);
        let sorted_right = Self::ms_sort_i64(&right);
        let result = Self::ms_merge_i64(&sorted_left, &sorted_right);
        result
    }

    pub fn max_sum_range_query(nums: Vec<i32>, requests: Vec<Vec<i32>>) -> i32 {
        let n = nums.len();
        let m = requests.len();
        let modval: i64 = 1_000_000_007;
        let mut diff: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z < n {
            diff.push(0);
            z = z + 1;
        }
        let mut r: usize = 0;
        while r < m {
            let s = requests[r][0] as usize;
            let e = requests[r][1] as usize;
            diff[s] = diff[s] + 1;
            if e + 1 < n {
                diff[e + 1] = diff[e + 1] - 1;
            }
            r = r + 1;
        }
        let mut count: Vec<i64> = Vec::new();
        let mut running: i64 = 0;
        let mut idx: usize = 0;
        while idx < n {
            running = running + diff[idx];
            count.push(running);
            idx = idx + 1;
        }
        let nums = Self::ms_sort(&nums);
        let sorted_count = Self::ms_sort_i64(&count);
        let mut result: i64 = 0;
        let mut k: usize = 0;
        while k < n {
            result = (result + nums[k] as i64 * sorted_count[k]) % modval;
            k = k + 1;
        }
        result as i32
    }
}
