impl Solution {
    fn is_symmetric(x: i32) -> bool {
        if x >= 10 && x <= 99 {
            x / 10 == x % 10
        } else if x >= 1000 && x <= 9999 {
            let left = x / 1000 + (x / 100) % 10;
            let right = (x / 10) % 10 + x % 10;
            left == right
        } else {
            false
        }
    }

    pub fn count_symmetric_integers(low: i32, high: i32) -> i32 {
        let mut i = low;
        let mut count = 0i32;
        while i <= high {
            let is_sym = Self::is_symmetric(i);
            if is_sym {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}
