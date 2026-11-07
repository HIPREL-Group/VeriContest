impl Solution {
    pub fn gravity_flip(a: Vec<i32>, n: usize) -> Vec<i32> {
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
        arr
    }
}
