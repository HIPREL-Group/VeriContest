impl Solution {
    pub fn min_ops_to_all_zero(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut cnt: Vec<i32> = Vec::new();
        let mut t = 0usize;
        while t < 101 {
            cnt.push(0i32);
            t = t + 1;
        }
        let mut i = 0usize;
        while i < n {
            let x = a[i] as usize;
            let prev = cnt[x];
            cnt[x] = prev + 1;
            i = i + 1;
        }
        let zc = cnt[0];
        if zc > 0 {
            return n as i32 - zc;
        }
        let mut v = 0usize;
        let mut dup = false;
        while v < 101 {
            if cnt[v] >= 2 {
                dup = true;
            }
            v = v + 1;
        }
        if dup {
            return n as i32;
        }
        (n as i32) + 1
    }
}
