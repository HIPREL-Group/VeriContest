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
    }
}

}
