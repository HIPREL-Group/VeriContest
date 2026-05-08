impl Solution {
    pub fn answer_queries(a: Vec<i8>, qls: Vec<usize>, qrs: Vec<usize>) -> Vec<u8> {
        let n = a.len();
        let m = qls.len();
        let mut pos: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 1i8 {
                pos = pos + 1;
            }
            i = i + 1;
        }
        let neg = n - pos;
        let mut out: Vec<u8> = Vec::new();
        let mut k: usize = 0;
        while k < m {
            let l = qls[k];
            let r = qrs[k];
            let len = r - l + 1;
            let half = len / 2;
            if len % 2 == 0 && half <= pos && half <= neg {
                out.push(1u8);
            } else {
                out.push(0u8);
            }
            k = k + 1;
        }
        out
    }
}
