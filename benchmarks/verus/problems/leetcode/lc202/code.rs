impl Solution {
    pub fn digit_sq(d: u128) -> u128
    {
        if d == 0 {
            0
        } else if d == 1 {
            1
        } else if d == 2 {
            4
        } else if d == 3 {
            9
        } else if d == 4 {
            16
        } else if d == 5 {
            25
        } else if d == 6 {
            36
        } else if d == 7 {
            49
        } else if d == 8 {
            64
        } else {
            81
        }
    }

    fn next_num(x: u128) -> u128
    {
        let mut tmp: u128 = x;
        let mut sum: u128 = 0;
        let mut cnt: usize = 0;
        while cnt < 10
        {
            let digit = tmp % 10;
            let sq = Self::digit_sq(digit);
            sum = sum + sq;
            tmp = tmp / 10;
            cnt = cnt + 1;
        }
        sum
    }

    pub fn is_happy(n: i32) -> bool
    {
        let start = n as u128;
        let mut value = start;
        let mut steps: usize = 0;
        while steps < 1000
        {
            let old_steps = steps;
            let old_value = value;
            value = Self::next_num(value);
            steps = steps + 1;
        }
        value == 1
    }
}
