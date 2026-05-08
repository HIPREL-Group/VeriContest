impl Solution {
    pub fn busy_student(start_time: Vec<i32>, end_time: Vec<i32>, query_time: i32) -> i32 {
        let mut count: i32 = 0;
        let n = start_time.len();
        let mut i: usize = 0;
        while i < n {
            if start_time[i] <= query_time && query_time <= end_time[i] {
                count += 1;
            }
            i += 1;
        }
        count
    }
}
