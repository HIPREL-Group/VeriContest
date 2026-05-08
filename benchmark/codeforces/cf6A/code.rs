impl Solution {
    pub fn has_triangle(sticks: Vec<i32>) -> bool {
        let mut found = false;
        let mut i = 0usize;
        while i < 4 {
            let mut j = 0usize;
            while j < 4 {
                let mut k = 0usize;
                while k < 4 {
                    if i != j && i != k && j != k {
                        let a = sticks[i] as i64;
                        let b = sticks[j] as i64;
                        let c = sticks[k] as i64;
                        if a + b > c && a + c > b && b + c > a {
                            found = true;
                        }
                    }
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        found
    }
}