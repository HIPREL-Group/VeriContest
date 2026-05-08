impl Solution {
    pub const MOD: i64 = 1_000_000_007;

    pub fn num_rolls_to_target(n: i32, k: i32, target: i32) -> i32 {
        let t = target as usize;
        let mut prev: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx <= t {
            prev.push(0i64);
            idx = idx + 1;
        }
        prev[0] = 1i64;
        let mut die: i32 = 0;
        while die < n {
            let mut curr: Vec<i64> = Vec::new();
            let mut idx2: usize = 0;
            while idx2 <= t {
                curr.push(0i64);
                idx2 = idx2 + 1;
            }
            let mut running_sum: i64 = 0;
            let mut j: usize = 1;
            while j <= t {
                running_sum = (running_sum + prev[j - 1]) % Self::MOD;
                if j > k as usize {
                    running_sum = (running_sum - prev[j - 1 - k as usize] + Self::MOD) % Self::MOD;
                }
                curr[j] = running_sum;
                j = j + 1;
            }
            prev = curr;
            die = die + 1;
        }
        prev[t] as i32
    }
}
