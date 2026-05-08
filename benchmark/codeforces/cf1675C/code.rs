impl Solution {
    pub fn count_suspects(s: Vec<u8>) -> usize {
        let n = s.len();
        let mut last_one: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] == 1u8 {
                last_one = i;
            }
            i += 1;
        }
        let mut first_zero: usize = n - 1;
        let mut j: usize = 0;
        let mut found_zero: bool = false;
        while j < n {
            if s[j] == 0u8 && !found_zero {
                first_zero = j;
                found_zero = true;
            }
            j += 1;
        }
        first_zero - last_one + 1
    }
}
