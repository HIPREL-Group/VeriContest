impl Solution {
    pub fn min_last_exam_day(exams: Vec<(i64, i64)>) -> i64 {
        let mut last_day = exams[0].1;
        let mut i = 1usize;
        while i < exams.len() {
            let a = exams[i].0;
            let b = exams[i].1;
            if b >= last_day {
                last_day = b;
            } else {
                last_day = a;
            }
            i += 1;
        }
        last_day
    }
}
