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
        let mut y = n + 1;
        while y <= 9999 {
            let d0 = y % 10;
            let d1 = (y / 10) % 10;
            let d2 = (y / 100) % 10;
            let d3 = (y / 1000) % 10;
            if d0 != d1 && d0 != d2 && d0 != d3 && d1 != d2 && d1 != d3 && d2 != d3 {
                return y;
            }
            y += 1;
        }
        y
    }
}

}
