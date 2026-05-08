use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn valid_count(num: int, k: int, c: int) -> bool
    recommends
        0 <= num,
        0 <= k <= 9,
{
    1 <= c <= 10 && c * k <= num && (c * k) % 10 == num % 10
}

pub open spec fn minimum_numbers_spec(num: int, k: int) -> int
    recommends
        0 <= num,
        0 <= k <= 9,
{
    if num == 0 {
        0
    } else if valid_count(num, k, 1) {
        1
    } else if valid_count(num, k, 2) {
        2
    } else if valid_count(num, k, 3) {
        3
    } else if valid_count(num, k, 4) {
        4
    } else if valid_count(num, k, 5) {
        5
    } else if valid_count(num, k, 6) {
        6
    } else if valid_count(num, k, 7) {
        7
    } else if valid_count(num, k, 8) {
        8
    } else if valid_count(num, k, 9) {
        9
    } else if valid_count(num, k, 10) {
        10
    } else {
        -1
    }
}

impl Solution {
    pub fn minimum_numbers(num: i32, k: i32) -> (result: i32)
        requires
            0 <= num <= 3000,
            0 <= k <= 9,
        ensures
            result as int == minimum_numbers_spec(num as int, k as int),
    {
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

}
