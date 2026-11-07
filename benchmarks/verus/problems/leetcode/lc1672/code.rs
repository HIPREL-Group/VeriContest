impl Solution {
    pub fn maximum_wealth(accounts: Vec<Vec<i32>>) -> i32 {
        let mut max_wealth: i32 = 0;
        let mut i: usize = 0;
        while i < accounts.len() {
            let mut wealth: i32 = 0;
            let mut j: usize = 0;
            while j < accounts[i].len() {
                wealth += accounts[i][j];
                j += 1;
            }
            if wealth > max_wealth {
                max_wealth = wealth;
            }
            i += 1;
        }
        max_wealth
    }
}
