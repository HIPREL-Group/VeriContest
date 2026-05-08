impl Solution {
    pub fn workout_sums(a: Vec<i64>) -> (i64, i64, i64) {
        let n = a.len();
        let mut chest: i64 = 0;
        let mut biceps: i64 = 0;
        let mut back: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let idx = i;
            if idx % 3 == 0 {
                chest = chest + a[idx];
            } else if idx % 3 == 1 {
                biceps = biceps + a[idx];
            } else {
                back = back + a[idx];
            }
            i = idx + 1;
        }
        (chest, biceps, back)
    }
}
