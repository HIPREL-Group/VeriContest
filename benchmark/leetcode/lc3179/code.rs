impl Solution {
    pub fn value_after_k_seconds(n: i32, k: i32) -> i32 {
        let m = n as usize;
        let modu = 1_000_000_007i64;
        let mut a: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < m {
            a.push(1);
            j += 1;
        }

        let mut t = 0i32;
        while t < k {
            let mut i = 1usize;
            while i < m {
                let cur = a[i];
                let prev = a[i - 1];
                let sum = cur + prev;
                a[i] = sum % modu;
                i += 1;
            }
            t += 1;
        }
        a[m - 1] as i32
    }
}
