impl Solution {
    pub fn can_paint_wall(m: usize, row0: Vec<i64>, row1: Vec<i64>) -> bool {
        let mut dp0: bool;
        let mut dp1: bool;
        if row0[0] == 1 && row1[0] == 0 {
            dp0 = true;
            dp1 = false;
        } else if row0[0] == 0 && row1[0] == 1 {
            dp0 = false;
            dp1 = true;
        } else {
            dp0 = true;
            dp1 = true;
        }
        let mut j: usize = 1;
        while j < m {
            let new_dp0: bool;
            let new_dp1: bool;
            if row0[j] == 1 && row1[j] == 0 {
                new_dp0 = dp0;
                new_dp1 = false;
            } else if row0[j] == 0 && row1[j] == 1 {
                new_dp0 = false;
                new_dp1 = dp1;
            } else {
                new_dp0 = dp1;
                new_dp1 = dp0;
            }
            dp0 = new_dp0;
            dp1 = new_dp1;
            j = j + 1;
        }
        dp0 || dp1
    }
}
