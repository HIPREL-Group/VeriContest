impl Solution {
    fn count_digit_exec(nums: &Vec<i32>, digit: i32) -> i32 {
        let n = nums.len();
        let mut i: usize = 0;
        let mut c: i32 = 0;
        while i < n {
            if nums[i] == digit {
                c = c + 1;
            }
            i = i + 1;
        }
        c
    }

    fn need_count_exec(num: i32, digit: i32) -> i32 {
        let h = num / 100;
        let t = (num / 10) % 10;
        let u = num % 10;
        let mut c: i32 = 0;
        if h == digit {
            c = c + 1;
        }
        if t == digit {
            c = c + 1;
        }
        if u == digit {
            c = c + 1;
        }
        c
    }

    fn can_form_exec(nums: &Vec<i32>, num: i32) -> bool {
        let mut d: i32 = 0;
        let mut ok = true;
        while d <= 9 {
            let need = Self::need_count_exec(num, d);
            let have = Self::count_digit_exec(nums, d);
            if need > have {
                ok = false;
            }
            d = d + 1;
        }
        ok
    }

    pub fn find_even_numbers(digits: Vec<i32>) -> Vec<i32> {
        let mut result: Vec<i32> = Vec::new();
        let mut step: i32 = 0;
        while step < 450 {
            let num = 100 + 2 * step;
            if Self::can_form_exec(&digits, num) {
                result.push(num);
            }
            step = step + 1;
        }
        result
    }
}
