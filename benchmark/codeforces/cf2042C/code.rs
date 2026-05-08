impl Solution {
    fn zero_vec(size: usize) -> Vec<i64> {
        let mut res: Vec<i64> = Vec::new();
        let mut fill: usize = 0;
        while fill < size {
            res.push(0);
            fill = fill + 1;
        }
        res
    }

    fn build_gain_counts(owners: &Vec<i64>) -> Vec<i64> {
        let n = owners.len();
        let mut counts: Vec<i64> = Solution::zero_vec(n + 1);
        let mut suffix: i64 = 0;
        let mut i: usize = n;
        while i > 1 {
            let i0 = i - 1;
            if owners[i0] == 1 {
                suffix = suffix + 1;
            } else {
                suffix = suffix - 1;
            }
            if suffix > 0 {
                counts[suffix as usize] = counts[suffix as usize] + 1;
            }
            i = i0;
        }
        counts
    }

    pub fn minimum_groups(owners: Vec<i64>, k: i64) -> i64 {
        let n = owners.len();
        let counts = Solution::build_gain_counts(&owners);
        let mut gain: usize = n;
        let mut total: i64 = 0;
        let mut cuts: i64 = 0;
        while gain > 0 && total < k {
            let gain0 = gain;
            let gain_value = gain0 as i64;
            let total0 = total;
            let cuts0 = cuts;
            let need = (k - total + gain_value - 1) / gain_value;
            let take = if counts[gain0] < need { counts[gain0] } else { need };
            total = total0 + take * gain_value;
            cuts = cuts0 + take;
            gain = gain0 - 1;
        }
        if total < k {
            -1
        } else {
            cuts + 1
        }
    }
}
