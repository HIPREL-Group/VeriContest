impl Solution {
    pub fn verse_for_santa(n: usize, s: i64, a: Vec<i64>) -> i32 {
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + a[i];
            i = i + 1;
        }
        if total <= s {
            return 0;
        }
        let mut pref: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            pref = pref + a[j];
            if pref > s {
                let mut best_i: usize = 0;
                let mut t: usize = 1;
                while t <= j {
                    if a[t] > a[best_i] {
                        best_i = t;
                    }
                    t = t + 1;
                }
                return (best_i + 1) as i32;
            }
            j = j + 1;
        }
        0
    }
}
