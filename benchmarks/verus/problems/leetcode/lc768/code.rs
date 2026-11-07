impl Solution {
    pub fn max_chunks_to_sorted(arr: Vec<i32>) -> i32 {
        let n = arr.len();
        
        let mut suffix_min: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            suffix_min.push(arr[i]);
            i += 1;
        }
        
        if n > 1 {
            let mut i: usize = n - 1;
            while i > 0 {
                i -= 1;
                if suffix_min[i + 1] < suffix_min[i] {
                    suffix_min[i] = suffix_min[i + 1];
                }
            }
        }
        
        let mut chunks: i32 = 1;
        let mut prefix_max = arr[0];
        let mut i: usize = 0;
        while i < n - 1 {
            if arr[i] > prefix_max {
                prefix_max = arr[i];
            }
            if prefix_max <= suffix_min[i + 1] {
                chunks += 1;
            }
            i += 1;
        }
        chunks
    }
}
