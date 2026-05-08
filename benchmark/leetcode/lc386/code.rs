impl Solution {
    pub fn lexical_order(n: i32) -> Vec<i32> {
        let mut result: Vec<i32> = Vec::new();
        let mut curr: i32 = 1;
        let mut i: i32 = 0;
        while i < n
        {
            result.push(curr);
            curr = Self::lex_next_exec(curr, n);
            i += 1;
        }
        result
    }

    fn lex_next_exec(x: i32, n: i32) -> i32 {
        if x * 10 <= n {
            x * 10
        } else if x % 10 != 9 && x + 1 <= n {
            x + 1
        } else {
            Self::strip_trailing_zeros_exec((x / 10) + 1)
        }
    }

    fn strip_trailing_zeros_exec(mut y: i32) -> i32 {
        while y % 10 == 0 && y != 0
        {
            y = y / 10;
        }
        y
    }
}
