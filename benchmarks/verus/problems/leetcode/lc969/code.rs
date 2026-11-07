impl Solution {
    pub fn pancake_sort(arr: Vec<i32>) -> Vec<i32> {
        let mut a = arr;
        let n = a.len();
        let mut result: Vec<i32> = Vec::new();
        let mut x = n as i32;
        while x >= 1 {
            let mut i: usize = 0;
            while i < n && a[i] != x {
                i += 1;
            }
            let mut lo: usize = 0;
            let mut hi: usize = i;
            while lo < hi {
                let tmp = a[lo];
                a[lo] = a[hi];
                a[hi] = tmp;
                lo += 1;
                hi -= 1;
            }
            result.push((i + 1) as i32);
            let rev_len = (x - 1) as usize;
            lo = 0;
            hi = rev_len;
            while lo < hi {
                let tmp = a[lo];
                a[lo] = a[hi];
                a[hi] = tmp;
                lo += 1;
                hi -= 1;
            }
            result.push(x);
            x -= 1;
        }
        result
    }
}
