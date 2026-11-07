impl Solution {
    pub fn is_possible(n: usize, a: Vec<i32>, b: Vec<i32>) -> bool {
        let mut max_diff: i32 = 0;
        let mut i: usize = 0;
        let mut possible = true;
        
        while i < n {
            if a[i] < b[i] {
                possible = false;
            } else {
                let diff = a[i] - b[i];
                if diff > max_diff {
                    max_diff = diff;
                }
            }
            i += 1;
        }
        
        if !possible {
            return false;
        }
        
        let mut j: usize = 0;
        while j < n {
            let diff = a[j] - b[j];
            if diff < max_diff && b[j] != 0 {
                possible = false;
            }
            j += 1;
        }
        
        possible
    }
}
