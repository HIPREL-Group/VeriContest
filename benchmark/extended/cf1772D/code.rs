impl Solution {
    pub fn absolute_sorting(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut low: i64 = 0;
        let mut high: i64 = 1000000000;
        let mut i: usize = 0;
        while i + 1 < n {
            let x = a[i] as i64;
            let y = a[i + 1] as i64;
            if x < y {
                let ub = (x + y) / 2;
                if ub < high {
                    high = ub;
                }
            } else if x > y {
                let lb = (x + y + 1) / 2;
                if lb > low {
                    low = lb;
                }
            }
            i += 1;
        }
        if low <= high {
            low as i32
        } else {
            -1
        }
    }
}
