fn compute_sum(arr: &Vec<i32>, value: i32) -> i32 {
    let n = arr.len();
    let mut sum: i32 = 0;
    let mut j: usize = 0;
    while j < n {
        if arr[j] <= value {
            sum = sum + arr[j];
        } else {
            sum = sum + value;
        }
        j = j + 1;
    }
    sum
}

impl Solution {
    pub fn find_best_value(arr: Vec<i32>, target: i32) -> i32 {
        let n = arr.len();
        let mut max_val: i32 = arr[0];
        let mut i: usize = 1;
        while i < n {
            if arr[i] > max_val {
                max_val = arr[i];
            }
            i = i + 1;
        }
        let total_sum = compute_sum(&arr, max_val);
        if total_sum <= target {
            return max_val;
        }
        let mut lo: i32 = 0;
        let mut hi: i32 = max_val;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let sum_mid = compute_sum(&arr, mid);
            if sum_mid >= target {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        let sum_lo = compute_sum(&arr, lo);
        let sum_prev = compute_sum(&arr, lo - 1);
        if sum_lo - target < target - sum_prev {
            lo
        } else {
            lo - 1
        }
    }
}
