impl Solution {
    pub fn maximal_intersection_len(l: Vec<i64>, r: Vec<i64>) -> i64 {
        let n = l.len();
        let mut pre_l: Vec<i64> = Vec::new();
        let mut i = 0usize;
        while i < n {
            if i == 0 {
                pre_l.push(l[i]);
            } else {
                let pl = pre_l[i - 1];
                let li = l[i];
                let m = if li > pl { li } else { pl };
                pre_l.push(m);
            }
            i = i + 1;
        }
        let mut suf_l: Vec<i64> = Vec::new();
        let mut z = 0usize;
        while z < n {
            suf_l.push(0i64);
            z = z + 1;
        }
        let mut i2 = n;
        while i2 > 0 {
            i2 = i2 - 1;
            let idx = i2;
            if idx + 1 == n {
                suf_l[idx] = l[idx];
            } else {
                let sl = suf_l[idx + 1];
                let li = l[idx];
                suf_l[idx] = if li > sl { li } else { sl };
            }
        }
        let mut pre_r: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < n {
            if j == 0 {
                pre_r.push(r[j]);
            } else {
                let pr = pre_r[j - 1];
                let rj = r[j];
                let m = if rj < pr { rj } else { pr };
                pre_r.push(m);
            }
            j = j + 1;
        }
        let mut suf_r: Vec<i64> = Vec::new();
        let mut w = 0usize;
        while w < n {
            suf_r.push(0i64);
            w = w + 1;
        }
        let mut i3 = n;
        while i3 > 0 {
            i3 = i3 - 1;
            let idx = i3;
            if idx + 1 == n {
                suf_r[idx] = r[idx];
            } else {
                let sr = suf_r[idx + 1];
                let rj = r[idx];
                suf_r[idx] = if rj < sr { rj } else { sr };
            }
        }
        let mut ans = 0i64;
        let mut k = 0usize;
        while k < n {
            let ml = if k == 0 {
                suf_l[1]
            } else if k + 1 == n {
                pre_l[k - 1]
            } else {
                let a = pre_l[k - 1];
                let b = suf_l[k + 1];
                if a > b {
                    a
                } else {
                    b
                }
            };
            let mr = if k == 0 {
                suf_r[1]
            } else if k + 1 == n {
                pre_r[k - 1]
            } else {
                let a = pre_r[k - 1];
                let b = suf_r[k + 1];
                if a < b {
                    a
                } else {
                    b
                }
            };
            let cand = if ml > mr {
                0i64
            } else {
                mr.checked_sub(ml).unwrap()
            };
            if k == 0 {
                ans = cand;
            } else if cand > ans {
                ans = cand;
            }
            k = k + 1;
        }
        ans
    }
}
