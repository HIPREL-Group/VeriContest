use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit_at(y: int, pos: int) -> int
    recommends
        1000 <= y <= 9999,
        0 <= pos < 4,
{
    (y / (if pos == 0 { 1 } else if pos == 1 { 10 } else if pos == 2 { 100 } else { 1000 })) % 10
}

pub open spec fn distinct_digits(y: int) -> bool
    recommends 1000 <= y <= 9999,
{
    forall|i: int|
        0 <= i < 4 ==> forall|j: int|
            0 <= j < 4 && i != j ==> #[trigger] digit_at(y, i) != digit_at(y, j)
}

impl Solution {
    pub fn beautiful_year(n: i32) -> (res: i32)
        requires
            1000 <= n <= 9000,
        ensures
            res as int > n as int,
            1000 <= res as int <= 9999,
            distinct_digits(res as int),
            forall|k: int|
                (n as int) < k && k < (res as int) ==> !distinct_digits(k),
    {
    }
}

}
