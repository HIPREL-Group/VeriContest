impl Solution {
    pub fn minimum_numbers(num: i32, k: i32) -> i32 {
        if num == 0 {
            return 0;
        }

        if 1 * k <= num && (1 * k) % 10 == num % 10 {
            return 1;
        }
        if 2 * k <= num && (2 * k) % 10 == num % 10 {
            return 2;
        }
        if 3 * k <= num && (3 * k) % 10 == num % 10 {
            return 3;
        }
        if 4 * k <= num && (4 * k) % 10 == num % 10 {
            return 4;
        }
        if 5 * k <= num && (5 * k) % 10 == num % 10 {
            return 5;
        }
        if 6 * k <= num && (6 * k) % 10 == num % 10 {
            return 6;
        }
        if 7 * k <= num && (7 * k) % 10 == num % 10 {
            return 7;
        }
        if 8 * k <= num && (8 * k) % 10 == num % 10 {
            return 8;
        }
        if 9 * k <= num && (9 * k) % 10 == num % 10 {
            return 9;
        }
        if 10 * k <= num && (10 * k) % 10 == num % 10 {
            return 10;
        }

        -1
    }
}
