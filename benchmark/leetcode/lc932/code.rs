impl Solution {
    pub fn beautiful_array(n: i32) -> Vec<i32> {
        let mut res = Vec::new();
        res.push(1);
        while res.len() < n as usize {
            let mut next = Vec::new();
            let mut i = 0usize;
            while i < res.len() {
                next.push(2 * res[i] - 1);
                i = i + 1;
            }
            let mut j = 0usize;
            while j < res.len() {
                next.push(2 * res[j]);
                j = j + 1;
            }
            res = next;
        }
        let mut out = Vec::new();
        let mut idx = 0usize;
        while idx < res.len() {
            if res[idx] <= n {
                out.push(res[idx]);
            }
            idx = idx + 1;
        }
        out
    }
}
