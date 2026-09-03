impl Solution {
    pub fn kth_smallest_prime_fraction(arr: Vec<i32>, k: i32) -> Vec<i32>
    {
        let n = arr.len();
        let mut ptr: Vec<usize> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            ptr.push(0);
            idx += 1;
        }

        let mut ans_i: usize = 0;
        let mut ans_j: usize = 1;

        let mut t: i32 = 0;
        while t < k {
            let mut best_j: usize = 0;
            let mut j: usize = 1;
            while j < n {
                if ptr[j] < j {
                    let take = if best_j == 0 {
                        true
                    } else {
                        (arr[ptr[j]] as i64) * (arr[best_j] as i64) < (arr[ptr[best_j]] as i64) * (arr[j] as i64)
                    };
                    if take {
                        best_j = j;
                    }
                }
                j += 1;
            }

            ans_i = ptr[best_j];
            ans_j = best_j;
            ptr[best_j] = ptr[best_j] + 1;

            t += 1;
        }

        let mut result = Vec::new();
        result.push(arr[ans_i]);
        result.push(arr[ans_j]);
        result
    }
}
