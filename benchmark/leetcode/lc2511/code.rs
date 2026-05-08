impl Solution {
    pub fn capture_forts(forts: Vec<i32>) -> i32 {
        let mut best: i32 = 0;
        let mut i: usize = 0;

        while i < forts.len() {
            if forts[i] == 1 || forts[i] == -1 {
                let mut j: usize = i + 1;
                while j < forts.len() && forts[j] == 0 {
                    j = j + 1;
                }
                if j < forts.len() && forts[i] + forts[j] == 0 {
                    let count_usize = j - i - 1;
                    let count = count_usize as i32;
                    if count > best {
                        best = count;
                    }
                }
                if j > i + 1 {
                    i = j - 1;
                }
            }
            i = i + 1;
        }

        best
    }
}
