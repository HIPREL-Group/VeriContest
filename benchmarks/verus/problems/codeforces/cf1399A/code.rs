impl Solution {
    pub fn remove_smallest_possible(a: Vec<i32>) -> bool {
        let n = a.len();
        if n == 1 {
            return true;
        }
        let mut arr = Vec::new();
        let mut i = 0usize;
        while i < n {
            arr.push(a[i]);
            i += 1;
        }
        i = 0usize;
        while i < n {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n {
                if arr[j] < arr[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            if i != min_idx {
                let tmp = arr[i];
                arr[i] = arr[min_idx];
                arr[min_idx] = tmp;
            }
            i += 1;
        }
        let mut k = 0usize;
        while k + 1 < n {
            if (arr[k + 1] as i64) > (arr[k] as i64) + 1 {
                return false;
            }
            k += 1;
        }
        true
    }
}
