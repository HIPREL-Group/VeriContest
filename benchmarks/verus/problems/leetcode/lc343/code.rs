impl Solution {
    pub fn integer_break(n: i32) -> i32
    {
        if n == 2 {
            return 1;
        }
        if n == 3 {
            return 2;
        }
        let q = n / 3;
        let r = n % 3;
        let mut p: i32 = 1;
        let mut i: i32 = 0;

        if r == 0 {
            while i < q
            {
                p = p * 3;
                i += 1;
            }
            p
        } else if r == 1 {
            while i < q - 1
            {
                p = p * 3;
                i += 1;
            }
            p * 4
        } else {
            while i < q
            {
                p = p * 3;
                i += 1;
            }
            p * 2
        }
    }
}
