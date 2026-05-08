impl Solution {
    fn merge(a: &Vec<i32>, b: &Vec<i32>) -> Vec<i32> {
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

    fn merge_sort(nums: &Vec<i32>) -> Vec<i32> {
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
        while i < mid {
            left.push(nums[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n {
            right.push(nums[j]);
            j = j + 1;
        }
        let sorted_left = Self::merge_sort(&left);
        let sorted_right = Self::merge_sort(&right);
        let result = Self::merge(&sorted_left, &sorted_right);
        result
    }

    pub fn eliminate_maximum(dist: Vec<i32>, speed: Vec<i32>) -> i32 {
        let n = dist.len();
        let mut arrivals: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let arrival = (dist[i] + speed[i] - 1) / speed[i];
            arrivals.push(arrival);
            i = i + 1;
        }
        let sorted = Self::merge_sort(&arrivals);
        let mut t: usize = 0;
        while t < n {
            if sorted[t] <= t as i32 {
                return t as i32;
            }
            t = t + 1;
        }
        n as i32
    }
}
