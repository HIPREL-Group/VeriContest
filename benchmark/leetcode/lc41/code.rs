impl Solution {
    pub fn first_missing_positive(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let mut arr = nums;
        let n_i32 = n as i32;
        let mut i: usize = 0;
        while i < n {
            while arr[i] >= 1 && arr[i] <= n_i32
                && arr[(arr[i] as usize) - 1] != arr[i]
            {
                let j = (arr[i] as usize) - 1;
                let vi = arr[i];
                let vj = arr[j];
                arr[j] = vi;
                arr[i] = vj;
            }
            i += 1;
        }
        let mut k: usize = 0;
        while k < n {
            if arr[k] != (k as i32) + 1 {
                return (k as i32) + 1;
            }
            k += 1;
        }
        (n as i32) + 1
    }
}
