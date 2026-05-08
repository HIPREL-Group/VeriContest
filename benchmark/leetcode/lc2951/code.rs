impl Solution {
    pub fn find_peaks(mountain: Vec<i32>) -> Vec<i32> {
        let n = mountain.len();
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if i > 0 && i + 1 < n && mountain[i - 1] < mountain[i] && mountain[i] > mountain[i + 1] {
                result.push(i as i32);
            }
            i = i + 1;
        }
        result
    }
}
