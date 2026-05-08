impl Solution {
    pub fn find_different_ones(a: Vec<i64>, queries: Vec<(usize, usize)>) -> Vec<(i32, i32)> {
        let n = a.len();
        let mut nxt: Vec<usize> = Vec::with_capacity(n);
        let mut p: usize = 0;
        while p < n {
            nxt.push(n);
            p += 1;
        }
        let mut idx: usize = n - 1;
        while idx > 0 {
            let i = idx - 1;
            if a[i] != a[i + 1] {
                nxt[i] = i + 1;
            } else {
                nxt[i] = nxt[i + 1];
            }
            idx -= 1;
        }

        let mut ans: Vec<(i32, i32)> = Vec::with_capacity(queries.len());
        let mut qi: usize = 0;
        while qi < queries.len() {
            let l = queries[qi].0;
            let r = queries[qi].1;
            let li = l - 1;
            let j = nxt[li];
            if j < r {
                ans.push((l as i32, j as i32 + 1));
            } else {
                ans.push((-1, -1));
            }
            qi += 1;
        }
        ans
    }
}
