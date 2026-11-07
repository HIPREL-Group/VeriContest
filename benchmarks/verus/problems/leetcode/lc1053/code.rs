impl Solution {
    pub fn prev_perm_opt1(arr: Vec<i32>) -> Vec<i32> {
        let n = arr.len();
        if n <= 1 {
            return arr;
        }
        let mut arr = arr;
        let mut k = n - 1;
        while k >= 1 && arr[k - 1] <= arr[k] {
            k -= 1;
        }
        if k == 0 && arr[0] <= arr[1] {
            return arr;
        }
        let idx = k - 1;
        let mut j = n - 1;
        while j > idx + 1 && (arr[j] >= arr[idx] || arr[j] == arr[j - 1]) {
            j -= 1;
        }
        let val_j = arr[j];
        let val_idx = arr[idx];
        arr[idx] = val_j;
        arr[j] = val_idx;
        arr
    }
}
