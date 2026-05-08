impl Solution {
    pub fn light_switches(a: Vec<i32>, period: u32) -> i32 {
        let n = a.len();
        let kd: i64 = period as i64;
        let mut mx: i64 = a[0] as i64;
        let mut i: usize = 1;
        while i < n {
            let v: i64 = a[i] as i64;
            if v > mx {
                mx = v;
            }
            i = i + 1;
        }
        let t_end: i64 = mx + 2 * kd - 1;
        let mut t: i64 = mx;
        while t <= t_end {
            let mut ok: bool = true;
            let mut j: usize = 0;
            while j < n {
                let ai: i64 = a[j] as i64;
                let d: i64 = (t - ai) / kd;
                ok = ok && (d % 2 == 0);
                j = j + 1;
            }
            if ok {
                return t as i32;
            }
            t = t + 1;
        }
        -1
    }
}
