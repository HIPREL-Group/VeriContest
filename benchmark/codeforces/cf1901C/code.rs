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

    pub fn build_operations(a: Vec<i64>) -> Vec<i64> {
        let n = a.len();
        let mut mn = a[0];
        let mut mx = a[0];
        let mut idx: usize = 1;
        while idx < n {
            let cur = a[idx];
            if cur < mn {
                mn = cur;
            }
            if cur > mx {
                mx = cur;
            }
            idx += 1;
        }
        let steps = Self::steps_from_diff(mx - mn);
        let mut ops: Vec<i64> = Vec::new();
        let mut t: i64 = 0;
        while t < steps {
            let x = if mn % 2 == 1 && mx % 2 == 0 { 1 } else { 0 };
            ops.push(x);
            mn = (mn + x) / 2;
            mx = (mx + x) / 2;
            t += 1;
        }
        ops
    }
}
