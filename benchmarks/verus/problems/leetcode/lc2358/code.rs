impl Solution {
    pub fn maximum_groups(grades: Vec<i32>) -> i32 {
        let n = grades.len() as i32;
        let mut k: i32 = 0;
        let mut used: i32 = 0;

        while used + (k + 1) <= n {
            k = k + 1;
            used = used + k;
        }

        k
    }
}
