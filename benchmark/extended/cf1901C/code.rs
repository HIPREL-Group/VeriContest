impl Solution {
    pub fn steps_from_diff(d: i64) -> i64 {
        if d == 0 {
            0
        } else {
            let sub = Self::steps_from_diff(d / 2);
            sub + 1
        }
    }

    pub fn min_operations(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut mn = a[0];
        let mut mx = a[0];
        let mut i: usize = 1;
        while i < n {
            let cur = a[i];
            if cur < mn {
                mn = cur;
            }
            if cur > mx {
                mx = cur;
            }
            i += 1;
        }
        Self::steps_from_diff(mx - mn)
    }
}
