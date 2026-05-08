impl Solution {
    pub fn construct_gcd_array(n: usize, l: i32, r: i32) -> (bool, Vec<i32>) {
        let mut a: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t < n {
            a.push(0i32);
            t = t + 1;
        }
        let mut i: usize = 0;
        while i < n {
            let k = (i + 1) as i32;
            let k64 = k as i64;
            let num: i64 = l as i64 + k64 - 1;
            let q = num / k64;
            let first = (q * k64) as i32;
            if first > r {
                return (false, Vec::new());
            }
            a[i] = first;
            i = i + 1;
        }
        (true, a)
    }
}
