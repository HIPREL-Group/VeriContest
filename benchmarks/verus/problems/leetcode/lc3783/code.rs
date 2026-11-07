impl Solution {
    pub fn mirror_distance(n: i32) -> i32 {
        let mut cur: i32 = n;
        let mut rev: i32 = 0;

        while cur > 0 {
            let digit: i32 = cur % 10;
            match rev.checked_mul(10) {
                None => {
                    return n;
                }
                Some(tmp) => {
                    match tmp.checked_add(digit) {
                        None => {
                            return n;
                        }
                        Some(next) => {
                            rev = next;
                        }
                    }
                }
            }
            cur = cur / 10;
        }

        if n >= rev {
            n - rev
        } else {
            rev - n
        }
    }
}
