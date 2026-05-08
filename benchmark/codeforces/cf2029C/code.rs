impl Solution {
    fn rating_step(cur: i32, perf: i32) -> i32 {
        if perf > cur {
            cur + 1
        } else if perf < cur {
            cur - 1
        } else {
            cur
        }
    }

    pub fn max_rating(a: Vec<i32>) -> i32 {
        let n = a.len();
        let neg: i32 = i32::MIN / 4;
        let mut f0: i32 = 0;
        let mut f1: i32 = neg;
        let mut f2: i32 = neg;
        let mut i: usize = 0;
        while i < n {
            let ai = a[i];
            let new_f2 = Self::rating_step(f1, ai).max(Self::rating_step(f2, ai));
            let new_f1 = f1.max(f0);
            let new_f0 = Self::rating_step(f0, ai);
            f2 = new_f2;
            f1 = new_f1;
            f0 = new_f0;
            i = i + 1;
        }
        let res = f1.max(f2);
        res
    }
}
