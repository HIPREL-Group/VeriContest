impl Solution {
    pub fn second_min(a: Vec<i32>, n: usize) -> Option<i32> {
        let mut min_val: i32 = a[0];
        let mut i: usize = 1;
        while i < n {
            if a[i] < min_val {
                min_val = a[i];
            }
            i = i + 1;
        }
        let mut found: bool = false;
        let mut second: i32 = 0i32;
        let mut k: usize = 0;
        while k < n {
            if a[k] > min_val {
                if !found || a[k] < second {
                    second = a[k];
                    found = true;
                }
            }
            k = k + 1;
        }
        if found {
            Some(second)
        } else {
            None
        }
    }
}
