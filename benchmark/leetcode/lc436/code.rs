impl Solution {
    pub fn find_right_interval(intervals: Vec<Vec<i32>>) -> Vec<i32>
    {
        let n = intervals.len();
        let mut result: Vec<i32> = Vec::new();
        for i in 0..n
        {
            let mut min_start: i32 = 1_000_001;
            let mut ans: i32 = -1;

            for j in 0..n
            {
                if intervals[j][0] >= intervals[i][1] && intervals[j][0] < min_start {
                    min_start = intervals[j][0];
                    ans = j as i32;
                }
            }

            result.push(ans);
        }

        result
    }
}
