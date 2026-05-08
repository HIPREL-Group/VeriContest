impl Solution {
    pub fn relative_sort_array(arr1: Vec<i32>, arr2: Vec<i32>) -> Vec<i32> {
        let mut cnt: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < 1001 {
            cnt.push(0);
            i = i + 1;
        }

        let mut j: usize = 0;
        while j < arr1.len() {
            let v = arr1[j] as usize;
            cnt[v] = cnt[v] + 1;
            j = j + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < arr2.len() {
            let v = arr2[k];
            while cnt[v as usize] > 0 {
                result.push(v);
                cnt[v as usize] = cnt[v as usize] - 1;
            }
            k = k + 1;
        }

        let mut m: usize = 0;
        while m < 1001 {
            while cnt[m] > 0 {
                result.push(m as i32);
                cnt[m] = cnt[m] - 1;
            }
            m = m + 1;
        }

        result
    }
}
