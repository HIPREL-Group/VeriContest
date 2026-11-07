impl Solution {
    pub fn reverse(x: i32) -> i32
    {
        if x == i32::MIN {
            return 0;
        }
        let neg = x < 0;
        let mut cur: i32 = if neg { -x } else { x };
        let mut res: i32 = 0;

        while cur != 0
        {
            match res.checked_mul(10) {
                None => {
                    return 0;
                },
                Some(tmp) => match tmp.checked_add(cur % 10) {
                    None => {
                        return 0;
                    },
                    Some(fine) => {
                        res = fine;
                    },
                },
            }
            cur = cur / 10;
        }

        if neg {
            -res
        } else {
            res
        }
    }
}
