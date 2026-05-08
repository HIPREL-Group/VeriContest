impl Solution {
    pub fn construct_coeffs(a: Vec<i32>) -> Vec<i32> {
        let n = a.len();
        let mut b: Vec<i32> = Vec::new();

        if n % 2 == 1 {
            let x0 = a[0];
            let x1 = a[1];
            let x2 = a[2];
            if x0 + x1 != 0 {
                b.push(x2);
                b.push(x2);
                b.push(-(x0 + x1));
            } else if x0 + x2 != 0 {
                b.push(x1);
                b.push(-(x0 + x2));
                b.push(x1);
            } else {
                b.push(-(x1 + x2));
                b.push(x0);
                b.push(x0);
            }

            let mut i: usize = 3;
            while i < n {
                b.push(a[i + 1]);
                b.push(-a[i]);
                i = i + 2;
            }
        } else {
            let mut i: usize = 0;
            while i < n {
                b.push(a[i + 1]);
                b.push(-a[i]);
                i = i + 2;
            }
        }

        b
    }
}
