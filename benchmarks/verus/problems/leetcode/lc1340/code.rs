impl Solution {
    pub fn max_jumps(arr: Vec<i32>, d: i32) -> i32 {
        let n = arr.len();
        let du = d as usize;
        let mut order: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            order.push(i);
            i += 1;
        }
        i = 0;
        while i < n {
            let mut min_k = i;
            let mut j = i + 1;
            while j < n {
                if arr[order[j]] < arr[order[min_k]] {
                    min_k = j;
                }
                j += 1;
            }
            let tmp = order[i];
            order[i] = order[min_k];
            order[min_k] = tmp;
            i += 1;
        }
        let mut dp: Vec<i32> = Vec::new();
        i = 0;
        while i < n {
            dp.push(1i32);
            i += 1;
        }
        let mut k: usize = 0;
        while k < n {
            let idx = order[k];
            let mut best: i32 = 0;
            let mut j = idx + 1;
            while j < n && j <= idx + du {
                if arr[j] >= arr[idx] {
                    break;
                }
                if dp[j] > best {
                    best = dp[j];
                }
                j += 1;
            }
            let left_bound: usize = if idx >= du { idx - du } else { 0 };
            j = idx;
            while j > left_bound {
                j -= 1;
                if arr[j] >= arr[idx] {
                    break;
                }
                if dp[j] > best {
                    best = dp[j];
                }
            }
            dp[idx] = best + 1;
            k += 1;
        }
        let mut best_val = dp[0];
        i = 1;
        while i < n {
            if dp[i] > best_val {
                best_val = dp[i];
            }
            i += 1;
        }
        best_val
    }
}
