impl Solution {
    pub fn find_length_of_shortest_subarray(arr: Vec<i32>) -> i32 {
        let n = arr.len();
        let mut left: usize = 0;
        while left + 1 < n && arr[left] <= arr[left + 1] {
            left = left + 1;
        }
        if left + 1 == n {
            return 0;
        }
        let mut right: usize = n - 1;
        while right > 0 && arr[right - 1] <= arr[right] {
            right = right - 1;
        }
        let mut best: usize = if n - left - 1 < right {
            n - left - 1
        } else {
            right
        };
        let mut i: usize = 0;
        let mut j: usize = right;
        while i <= left && j < n {
            if arr[i] <= arr[j] {
                let candidate = j - i - 1;
                if candidate < best {
                    best = candidate;
                }
                i = i + 1;
            } else {
                j = j + 1;
            }
        }
        best as i32
    }
}
