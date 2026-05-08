impl Solution {
    pub fn optimal_tests(a: Vec<i64>, q: i64) -> Vec<u8> {
        let n = a.len();
        let mut cur_q: i64 = 0;
        let mut ans: Vec<u8> = Vec::new();
        let mut fill: usize = 0;
        while fill < n {
            ans.push(0);
            fill = fill + 1;
        }

        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            let aval = a[i];

            if aval <= cur_q {
                ans[i] = 1;
            } else if cur_q < q {
                cur_q = cur_q + 1;
                ans[i] = 1;
            } else {
                ans[i] = 0;
            }
        }
        ans
    }
}
