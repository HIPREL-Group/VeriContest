impl Solution {
    pub fn max_ones_after_flip(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut result = 0;
        let mut i = 0;
        while i < n {
            let mut j = i;
            while j < n {
                let mut count = 0;
                let mut k = 0;
                while k < n {
                    let val = if i <= k && k <= j {
                        1 - a[k]
                    } else {
                        a[k]
                    };
                    if val == 1 {
                        count = count + 1;
                    }
                    k = k + 1;
                }
                if count > result {
                    result = count;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        result
    }
}
