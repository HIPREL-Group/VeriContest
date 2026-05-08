impl Solution {
    fn zero_run_end(s: &Vec<i32>, i: usize) -> usize {
        let n = s.len();
        if i + 1 >= n {
            let j_end = i + 1;
            j_end
        } else {
            if s[i + 1] != 0 {
                let j_end = i + 1;
                j_end
            } else {
                Self::zero_run_end(s, i + 1)
            }
        }
    }

    pub fn min_total_seated_students(s: &Vec<i32>) -> i64 {
        let n = s.len();
        let mut ones: i64 = 0;
        let mut add: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] == 1 {
                ones = ones + 1;
                i = i + 1;
            } else {
                let j_end = Self::zero_run_end(s, i);
                let l: usize = j_end - i;
                let left: bool = if i > 0 {
                    s[i - 1] == 1
                } else {
                    false
                };
                let right: bool = if j_end < n {
                    s[j_end] == 1
                } else {
                    false
                };
                let extra: i64 = if left && right {
                    (l as i64) / 3
                } else if left || right {
                    ((l as i64) + 1) / 3
                } else {
                    ((l as i64) + 2) / 3
                };
                add = add + extra;
                i = j_end;
            }
        }
        ones + add
    }
}
