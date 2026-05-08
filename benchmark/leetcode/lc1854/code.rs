impl Solution {
    pub fn maximum_population(logs: Vec<Vec<i32>>) -> i32 {
        let n = logs.len();
        let mut best_year: i32 = 1950;
        let mut max_pop: i32 = 0;
        let mut year: i32 = 1950;
        while year <= 2049 {
            let mut pop: i32 = 0;
            let mut i: usize = 0;
            while i < n {
                if logs[i][0] <= year && year < logs[i][1] {
                    pop += 1;
                }
                i += 1;
            }
            if pop > max_pop {
                max_pop = pop;
                best_year = year;
            }
            year += 1;
        }
        best_year
    }
}
