impl Solution {
    pub fn max_count(banned: Vec<i32>, n: i32, max_sum: i32) -> i32 {
        let mut count: i32 = 0;
        let mut remain: i32 = max_sum;
        let mut x: i32 = 1;

        while x <= n {
            let mut is_banned: bool = false;
            let mut j: usize = 0;
            while j < banned.len() {
                if banned[j] == x {
                    is_banned = true;
                }
                j = j + 1;
            }

            if is_banned {
                x = x + 1;
                continue;
            }

            if x <= remain {
                remain = remain - x;
                count = count + 1;
                x = x + 1;
            } else {
                x = n + 1;
            }
        }

        count
    }
}
