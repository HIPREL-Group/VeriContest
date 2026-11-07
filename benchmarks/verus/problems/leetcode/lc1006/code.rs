impl Solution {
    pub fn clumsy(n: i32) -> i32 {
        if n == 1 { return 1; }
        if n == 2 { return 2; }
        if n == 3 { return 6; }

        let mut result = n * (n - 1) / (n - 2) + (n - 3);
        let mut k = n - 4;

        while k >= 4 {
            result = result - k * (k - 1) / (k - 2) + (k - 3);
            k = k - 4;
        }

        if k == 3 {
            result = result - k * (k - 1) / (k - 2);
        } else if k == 2 {
            result = result - k * (k - 1);
        } else if k == 1 {
            result = result - k;
        }

        result
    }
}
