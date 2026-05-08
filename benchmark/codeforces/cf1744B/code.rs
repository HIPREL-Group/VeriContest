impl Solution {
    pub fn even_odd_sums(a: Vec<u32>, n: usize, qtypes: Vec<u32>, qxs: Vec<u32>, q: usize) -> Vec<i64> {
        let mut sum: i64 = 0;
        let mut ce: i64 = 0;
        let mut co: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            sum += a[i] as i64;
            if a[i] % 2 == 0 {
                ce += 1;
            } else {
                co += 1;
            }
            i += 1;
        }
        let mut result: Vec<i64> = Vec::with_capacity(q);
        let mut k: usize = 0;
        while k < q {
            let t = qtypes[k];
            let x = qxs[k] as i64;
            if t == 0 {
                sum += ce * x;
                if x % 2 == 1 {
                    co += ce;
                    ce = 0;
                }
            } else {
                sum += co * x;
                if x % 2 == 1 {
                    ce += co;
                    co = 0;
                }
            }
            result.push(sum);
            k += 1;
        }
        result
    }
}
