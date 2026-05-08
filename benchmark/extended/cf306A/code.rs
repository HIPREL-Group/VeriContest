impl Solution {
    pub fn fair_candy_split(n: i32, m: i32) -> Vec<i32> {
        let base = n / m;
        let rem = n % m;
        let mut v: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mu = m as usize;
        while i < mu {
            let val = if i < rem as usize { base + 1 } else { base };
            v.push(val);
            i = i + 1;
        }
        v
    }
}
