impl Solution {
    pub fn find_closest_elements(arr: Vec<i32>, k: i32, x: i32) -> Vec<i32> {
        let n = arr.len();
        let k_usize = k as usize;
        if x <= arr[0] {
            let mut res = Vec::new();
            let mut i: usize = 0;
            while i < k_usize {
                res.push(arr[i]);
                i += 1;
            }
            res
        } else if x >= arr[n - 1] {
            let mut res = Vec::new();
            let start = n - k_usize;
            let mut i = start;
            while i < n {
                res.push(arr[i]);
                i += 1;
            }
            res
        } else {
            let mut low: usize = 0;
            let mut high = n - k_usize;
            while low < high {
                let mid = low + (high - low) / 2;
                let left_dist = x as i64 - arr[mid] as i64;
                let right_dist = arr[mid + k_usize] as i64 - x as i64;
                if left_dist > right_dist {
                    low = mid + 1;
                } else {
                    high = mid;
                }
            }
            let mut res = Vec::new();
            let mut i = low;
            while i < low + k_usize {
                res.push(arr[i]);
                i += 1;
            }
            res
        }
    }
}
