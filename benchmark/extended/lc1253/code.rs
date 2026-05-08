impl Solution {
    pub fn reconstruct_matrix(upper: i32, lower: i32, colsum: Vec<i32>) -> Vec<Vec<i32>> {
        let n = colsum.len();
        let mut ones: i32 = 0;
        let mut twos: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if colsum[i] == 1 {
                ones += 1;
            } else if colsum[i] == 2 {
                twos += 1;
            }
            i += 1;
        }
        if twos > upper || twos > lower {
            return Vec::new();
        }
        let upper_ones = upper - twos;
        let lower_ones = lower - twos;
        if upper_ones + lower_ones != ones {
            return Vec::new();
        }
        let mut top: Vec<i32> = Vec::new();
        let mut bottom: Vec<i32> = Vec::new();
        let mut rem_upper_ones = upper_ones;
        let mut j: usize = 0;
        while j < n {
            if colsum[j] == 2 {
                top.push(1);
                bottom.push(1);
            } else if colsum[j] == 1 {
                if rem_upper_ones > 0 {
                    top.push(1);
                    bottom.push(0);
                    rem_upper_ones -= 1;
                } else {
                    top.push(0);
                    bottom.push(1);
                }
            } else {
                top.push(0);
                bottom.push(0);
            }
            j += 1;
        }
        let mut result: Vec<Vec<i32>> = Vec::new();
        result.push(top);
        result.push(bottom);
        result
    }
}
