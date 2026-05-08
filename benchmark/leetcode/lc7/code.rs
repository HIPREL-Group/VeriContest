impl Solution {
    pub fn reverse(x: u32) -> u32 {
        let mut res: u32 = 0;
        let mut cur: u32 = x;

        while cur != 0 {
            match res.checked_mul(10) {
                None => return 0,
                Some(tmp) => match tmp.checked_add(cur % 10) {
                    None => return 0,
                    Some(fine) => {
                        res = fine;
                    }
                },
            }
            cur = cur / 10;
        }

        res
    }
}
