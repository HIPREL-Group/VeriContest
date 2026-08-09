fn digit_at_exec(n: i32, p: usize) -> usize {
    if p == 0 {
        (n % 10) as usize
    } else {
        digit_at_exec(n / 10, p - 1)
    }
}

impl Solution {
    pub fn sum_digit_differences(nums: Vec<i32>) -> i64 {
        let n = nums.len();
        let mut cnt: Vec<Vec<i64>> = Vec::new();
        let mut pi: usize = 0;
        while pi < 9 {
            let mut drow: Vec<i64> = Vec::new();
            let mut di: usize = 0;
            while di < 10 {
                drow.push(0);
                di += 1;
            }
            cnt.push(drow);
            pi += 1;
        }

        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let x = nums[i];
            let mut contrib: i64 = 0;
            let mut p: usize = 0;
            while p < 9 {
                let d = digit_at_exec(x, p);
                let matching = cnt[p][d];
                let term = (i as i64) - matching;
                contrib = contrib + term;
                p += 1;
            }

            let mut p2: usize = 0;
            while p2 < 9 {
                let d2 = digit_at_exec(x, p2);
                let old_val = cnt[p2][d2];
                let mut row = cnt[p2].clone();
                row[d2] = old_val + 1;
                cnt[p2] = row;
                p2 += 1;
            }

            total = total + contrib;
            i += 1;
        }

        total
    }
}
