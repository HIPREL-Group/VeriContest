impl Solution {
    pub fn optimal_score(a: Vec<i64>, k: i64) -> u64 {
        let n = a.len();
        let mut i: usize = 0;
        let mut cur_k: i64 = k;
        let mut answer: u64 = 0;

        while i < n {
            if i + 1 == n {
                answer = answer + a[i] as u64;
                i = i + 1;
            } else {
                let diff = a[i] - a[i + 1];
                if cur_k >= diff {
                    cur_k = cur_k - diff;
                } else {
                    answer = answer + (diff - cur_k) as u64;
                    cur_k = 0;
                }
                i = i + 2;
            }
        }

        answer
    }
}
