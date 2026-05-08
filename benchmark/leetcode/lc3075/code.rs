impl Solution {
    pub fn maximum_happiness_sum(happiness: Vec<i32>, k: i32) -> i64 {
        let mut a = happiness;
        let n = a.len();
        let ku = k as usize;

        let mut ans: i64 = 0;
        let mut taken: i32 = 0;
        let mut round: usize = 0;
        while round < ku {
            let mut max_idx: usize = 0;
            let mut j: usize = 1;
            while j < n {
                if a[j] >= a[max_idx] {
                    max_idx = j;
                }
                j = j + 1;
            }

            let val = a[max_idx];
            let gain = val - taken;
            if gain > 0 {
                ans = ans + gain as i64;
            }

            a[max_idx] = -1;
            taken = taken + 1;
            round = round + 1;
        }

        ans
    }
}
