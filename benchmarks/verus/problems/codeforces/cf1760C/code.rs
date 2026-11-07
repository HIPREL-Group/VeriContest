impl Solution {
    pub fn advantages(s: Vec<i64>) -> Vec<i64> {
        let n = s.len();
        let mut max1: i64 = s[0];
        let mut idx1: usize = 0;
        let mut max2: i64 = s[1];
        let mut idx2: usize = 1;

        if max2 > max1 {
            let tv = max1;
            let ti = idx1;
            max1 = max2;
            idx1 = idx2;
            max2 = tv;
            idx2 = ti;
        }

        let mut t: usize = 2;
        while t < n {
            if s[t] > max1 {
                max2 = max1;
                idx2 = idx1;
                max1 = s[t];
                idx1 = t;
            } else if s[t] > max2 {
                max2 = s[t];
                idx2 = t;
            }
            t = t + 1;
        }

        let mut result: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            let best: i64;
            if i == idx1 {
                best = max2;
            } else {
                best = max1;
            }

            result.push(s[i] - best);
            i = i + 1;
        }

        result
    }
}
