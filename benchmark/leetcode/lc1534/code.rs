impl Solution {
    pub fn count_good_triplets(arr: Vec<i32>, a: i32, b: i32, c: i32) -> i32 {
        let n = arr.len();
        let mut count: u32 = 0;
        let mut k: usize = 2;
        while k < n {
            let count_before_k: u32 = count;
            let mut j: usize = 1;
            while j < k {
                let count_before_j: u32 = count;
                let mut i: usize = 0;
                while i < j {
                    let diff_ij: i32 = if arr[i] >= arr[j] { arr[i] - arr[j] } else { arr[j] - arr[i] };
                    let diff_jk: i32 = if arr[j] >= arr[k] { arr[j] - arr[k] } else { arr[k] - arr[j] };
                    let diff_ik: i32 = if arr[i] >= arr[k] { arr[i] - arr[k] } else { arr[k] - arr[i] };
                    let inside = diff_ij <= a && diff_jk <= b && diff_ik <= c;
                    if inside {
                        count += 1;
                    }
                    i += 1;
                }
                j += 1;
            }
            k += 1;
        }
        count as i32
    }
}
