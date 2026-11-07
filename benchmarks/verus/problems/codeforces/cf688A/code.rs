impl Solution {
    fn is_win_row(row: &Vec<u8>) -> bool {
        let n = row.len();
        let mut j = 0usize;
        let mut found = false;
        while j < n {
            if row[j] == 48u8 {
                found = true;
            }
            j = j + 1;
        }
        found
    }

    pub fn max_consecutive_winning_days(n: usize, d: usize, days: &Vec<Vec<u8>>) -> usize {
        let _ = n;
        let mut best = 0usize;
        let mut cur = 0usize;
        let mut i = 0usize;
        while i < d {
            if Solution::is_win_row(&days[i]) {
                cur = cur + 1;
            } else {
                cur = 0;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}
