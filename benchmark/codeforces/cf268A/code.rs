impl Solution {
    pub fn count_host_guest_uniforms(home: Vec<i32>, away: Vec<i32>, n: usize) -> usize {
        let mut count = 0usize;
        let mut i = 0usize;
        while i < n {
            let mut j = 0usize;
            while j < n {
                if i != j && home[i] == away[j] {
                    count += 1;
                }
                j += 1;
            }
            i += 1;
        }
        count
    }
}
