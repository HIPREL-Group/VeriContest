impl Solution {
    pub fn good_days_to_rob_bank(security: Vec<i32>, time: i32) -> Vec<i32> {
        let n = security.len();
        let mut inc_prefix: Vec<i32> = Vec::new();
        let mut dec_prefix: Vec<i32> = Vec::new();
        inc_prefix.push(0);
        dec_prefix.push(0);

        let mut i: usize = 1;
        while i < n {
            let mut inc_next = inc_prefix[i - 1];
            let prev = security[i - 1];
            let curr = security[i];
            if prev < curr {
                inc_next = inc_next + 1;
            }

            let mut dec_next = dec_prefix[i - 1];
            if prev > curr {
                dec_next = dec_next + 1;
            }

            inc_prefix.push(inc_next);
            dec_prefix.push(dec_next);

            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut day: usize = 0;
        while day < n {
            let day_i = day as i32;
            if time <= day_i
                && day_i + time < n as i32
                && inc_prefix[day] == inc_prefix[(day_i - time) as usize]
                && dec_prefix[(day_i + time) as usize] == dec_prefix[day]
            {
                result.push(day_i);
            }
            day += 1;
        }

        result
    }
}
