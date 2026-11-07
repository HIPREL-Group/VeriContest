impl Solution {
    pub fn num_of_subarrays(arr: Vec<i32>, k: i32, threshold: i32) -> i32 {
        let n = arr.len();
        let k_usize = k as usize;
        let mut sum = 0i64;
        let mut i = 0usize;
        while i < k_usize {
            sum += arr[i] as i64;
            i += 1;
        }
        let tk: i64 = threshold as i64 * k as i64;
        let mut count = 0i32;
        if sum >= tk {
            count += 1;
        }
        let mut i = k_usize;
        while i < n {
            sum += arr[i] as i64;
            sum -= arr[i - k_usize] as i64;
            if sum >= tk {
                count += 1;
            }
            i += 1;
        }
        count
    }
}
