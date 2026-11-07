impl Solution {
    pub fn odd_queries(
        a: Vec<u32>,
        n: usize,
        ls: Vec<u32>,
        rs: Vec<u32>,
        ks: Vec<u32>,
        q: usize,
    ) -> Vec<bool> {
        let mut prefix: Vec<i64> = Vec::with_capacity(n + 1);
        prefix.push(0i64);
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            s += a[i] as i64;
            prefix.push(s);
            i += 1;
        }
        let pref_n: i64 = prefix[n];
        let mut result: Vec<bool> = Vec::with_capacity(q);
        let mut j: usize = 0;
        while j < q {
            let l = ls[j] as usize;
            let r = rs[j] as usize;
            let k_val = ks[j] as i64;
            let count: i64 = (r - l + 1) as i64;
            let pref_l_minus_1 = prefix[l - 1];
            let pref_r_v = prefix[r];
            let outside: i64 = pref_l_minus_1 + (pref_n - pref_r_v);
            let mid: i64 = k_val * count;
            let total: i64 = outside + mid;
            let answer: bool = total % 2 == 1;
            result.push(answer);
            j += 1;
        }
        result
    }
}
