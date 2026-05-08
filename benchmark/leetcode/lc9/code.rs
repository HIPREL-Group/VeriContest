impl Solution {
    pub fn is_palindrome(x: i32) -> bool {
        if x < 0 {
            return false;
        }
        let x_unsigned = x as u32;
        let mut cur = x_unsigned;
        let mut rev = 0u32;
        while cur != 0 {
            rev =
            match rev.checked_mul(10) {
                Some(r) => match r.checked_add(cur % 10) {
                    Some(n) => n,
                    None => {
                        return false;
                    },
                },
                None => {
                    return false;
                },
            };
            cur /= 10;
        }
        rev == x_unsigned
    }
}
