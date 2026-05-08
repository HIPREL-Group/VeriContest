impl Solution {
    fn digit_sum(x: i32) -> i32 {
        (x / 1000) + ((x / 100) % 10) + ((x / 10) % 10) + (x % 10)
    }

    fn even_contrib(x: i32) -> i32 {
        let s = Self::digit_sum(x);
        if s % 2 == 0 {
            1
        } else {
            0
        }
    }

    pub fn count_even(num: i32) -> i32 {
        let mut i: i32 = 1;
        let mut count: i32 = 0;
        while i <= num {
            let add = Self::even_contrib(i);
            count = count + add;
            i = i + 1;
        }
        count
    }
}
