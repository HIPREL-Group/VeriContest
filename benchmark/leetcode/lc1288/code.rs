impl Solution {
    pub fn remove_covered_intervals(intervals: Vec<Vec<i32>>) -> i32 {
        let n = intervals.len();
        let mut count: i32 = 0;

        for i in 0..n {
            let mut covered = false;
            for j in 0..n {
                if j != i && intervals[j][0] <= intervals[i][0] && intervals[i][1] <= intervals[j][1] {
                    covered = true;
                }
            }
            if !covered {
                count += 1;
            }
        }
        count
    }
}
