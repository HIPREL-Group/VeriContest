impl Solution {
    pub fn max_chunks_to_sorted(arr: Vec<i32>) -> i32 {
        let mut max_so_far = 0i32;
        let mut chunks = 0i32;
        let mut i = 0usize;
        while i < arr.len() {
            if arr[i] > max_so_far {
                max_so_far = arr[i];
            }
            if max_so_far == i as i32 {
                chunks += 1;
            }
            i += 1;
        }
        chunks
    }
}
