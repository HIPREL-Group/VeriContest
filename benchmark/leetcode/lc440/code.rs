impl Solution {
    fn count_steps(n: i64, curr_in: i64, next_in: i64) -> i64 {
        let mut steps: i64 = 0;
        let mut curr = curr_in;
        let mut next = next_in;
        while curr <= n {
            let bound = if next <= n + 1 { next } else { n + 1 };
            steps = steps + (bound - curr);
            curr = curr * 10;
            next = next * 10;
        }
        steps
    }

    pub fn find_kth_number(n: i32, k: i32) -> i32 {
        let n64 = n as i64;
        let mut k_left: i64 = (k - 1) as i64;
        let mut curr: i64 = 1;
        while k_left > 0 {
            let steps = Self::count_steps(n64, curr, curr + 1);
            if steps <= k_left {
                curr = curr + 1;
                k_left = k_left - steps;
            } else {
                curr = curr * 10;
                k_left = k_left - 1;
            }
        }
        curr as i32
    }
}
