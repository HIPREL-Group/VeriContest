impl Solution {
    pub fn get_sum(n: i32) -> i64
    {
        let nn: i64 = n as i64;
        let mut sum: i64 = 0;
        let mut i: i64 = 1;

        while i * i <= nn
        {
            if nn % i == 0 {
                let comp: i64 = nn / i;
                sum = sum + i;
                if i != comp {
                    sum = sum + comp;
                }
            }

            i = i + 1;
        }

        sum - nn
    }

    pub fn check_perfect_number(num: i32) -> bool
    {
        if (num as i64) == Self::get_sum(num) {
            true
        }
        else {
            false
        }
    }
}
