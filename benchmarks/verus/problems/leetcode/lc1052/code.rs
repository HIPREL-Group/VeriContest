impl Solution {
    pub fn max_satisfied(customers: Vec<i32>, grumpy: Vec<i32>, minutes: i32) -> i32 {
        let n = customers.len();
        let m = minutes as usize;

        let mut base: i64 = 0;
        let mut i: usize = 0;
        while i < n
        {
            if grumpy[i] == 0 {
                base = base + customers[i] as i64;
            }
            i = i + 1;
        }

        let mut window: i64 = 0;
        let mut j: usize = 0;
        while j < m
        {
            if grumpy[j] == 1 {
                window = window + customers[j] as i64;
            }
            j = j + 1;
        }

        let mut max_window: i64 = window;
        let mut k: usize = m;

        while k < n
        {
            let new_right_val: i64 = if grumpy[k] == 1 {
                customers[k] as i64
            } else {
                0i64
            };
            let old_left_val: i64 = if grumpy[k - m] == 1 {
                customers[k - m] as i64
            } else {
                0i64
            };

            window = window + new_right_val - old_left_val;

            if window > max_window {
                max_window = window;
            }
            k = k + 1;
        }

        let result = (base + max_window) as i32;
        result
    }
}
