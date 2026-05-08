impl Solution {
    pub fn kth_smallest_prime_fraction(arr: Vec<i32>, k: i32) -> Vec<i32>
    {
        let n = arr.len();
        let target = k;

        let mut low = 0.0f64;
        let mut high = 1.0f64;
        let mut ans_num = arr[0];
        let mut ans_den = arr[n - 1];

        let mut iter = 0usize;
        while iter < 64
        {
            let mid = (low + high) / 2.0f64;
            let mut count = 0i32;
            let mut best_num = 0i32;
            let mut best_den = 1i32;

            let mut i = 0usize;
            let mut j = 1usize;
            while j < n
            {
                while i < j && (arr[i] as f64) <= mid * (arr[j] as f64)
                {
                    if (arr[i] as i64) * (best_den as i64) > (best_num as i64) * (arr[j] as i64) {
                        best_num = arr[i];
                        best_den = arr[j];
                    }
                    i += 1;
                }
                count += i as i32;
                j += 1;
            }

            if count < target {
                low = mid;
            } else {
                ans_num = best_num;
                ans_den = best_den;
                high = mid;
            }
            iter += 1;
        }

        vec![ans_num, ans_den]
    }
}
