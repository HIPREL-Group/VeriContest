impl Solution {
    pub fn can_erase_all(a: Vec<i64>) -> bool {
        let n = a.len();
        let mut i: usize = 0;

        while i < n {
            let mut ok = false;
            let mut d: i64 = 2;
            let lim: i64 = (i as i64) + 2;

            while d <= lim {
                if a[i] % d != 0 {
                    ok = true;
                }
                d = d + 1;
            }

            if !ok {
                return false;
            }

            i = i + 1;
        }

        true
    }
}
