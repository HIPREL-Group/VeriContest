impl Solution {
    fn check_no_zero(x: i32) -> bool {
        if x <= 0 {
            return false;
        }
        let mut val = x;
        while val >= 10 {
            if val % 10 == 0 {
                return false;
            }
            val = val / 10;
        }
        true
    }

    pub fn get_no_zero_integers(n: i32) -> Vec<i32> {
        let mut a: i32 = 1;
        while a < n {
            let b = n - a;
            if Self::check_no_zero(a) && Self::check_no_zero(b) {
                let mut res = Vec::new();
                res.push(a);
                res.push(b);
                return res;
            }
            a = a + 1;
        }
        let mut res = Vec::new();
        res.push(1);
        res.push(n - 1);
        res
    }
}
