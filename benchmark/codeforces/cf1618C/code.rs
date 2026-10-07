impl Solution {
    pub fn gcd_two(x: i64, y: i64) -> i64 {
        let mut x = x;
        let mut y = y;
        while y != 0 {
            let t = x % y;
            x = y;
            y = t;
        }
        x
    }

    pub fn paint_the_array(a: Vec<i64>) -> i64 {
        let n = a.len();
        let mut g_even = a[0];
        let mut i: usize = 2;
        while i < n {
            g_even = Self::gcd_two(g_even, a[i]);
            i = i + 2;
        }
        let mut g_odd = a[1];
        let mut i: usize = 3;
        while i < n {
            g_odd = Self::gcd_two(g_odd, a[i]);
            i = i + 2;
        }
        let mut ok_a = true;
        let mut j: usize = 1;
        while j < n {
            if a[j] % g_even == 0 {
                ok_a = false;
            }
            j = j + 2;
        }
        if ok_a {
            return g_even;
        }
        let mut ok_b = true;
        let mut j: usize = 0;
        while j < n {
            if a[j] % g_odd == 0 {
                ok_b = false;
            }
            j = j + 2;
        }
        if ok_b {
            return g_odd;
        }
        0
    }
}
