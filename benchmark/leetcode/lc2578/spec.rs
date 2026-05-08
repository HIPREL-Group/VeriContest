use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_count(n: int, d: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else { (if n % 10 == d { 1int } else { 0int }) + Self::digit_count(n / 10, d) }
    }

    pub open spec fn valid_split_sum(num: int, a: int, b: int) -> bool {
        a >= 0 && b >= 0
        && forall|d: int| 1 <= d <= 9 ==>
            #[trigger] Self::digit_count(num, d) == Self::digit_count(a, d) + Self::digit_count(b, d)
    }

    pub open spec fn digit_count_seq(n: int) -> Seq<int> {
        seq![
            Self::digit_count(n, 0), Self::digit_count(n, 1), Self::digit_count(n, 2),
            Self::digit_count(n, 3), Self::digit_count(n, 4), Self::digit_count(n, 5),
            Self::digit_count(n, 6), Self::digit_count(n, 7), Self::digit_count(n, 8),
            Self::digit_count(n, 9)
        ]
    }

    pub open spec fn greedy_sum(cnt: Seq<int>, d: int, a: int, b: int, turn_a: bool) -> int
        decreases 10 - d, if 0 <= d <= 9 && cnt.len() == 10 { cnt[d] } else { 0int },
    {
        if d < 0 || d > 9 || cnt.len() != 10 { a + b }
        else if cnt[d] <= 0 { Self::greedy_sum(cnt, d + 1, a, b, turn_a) }
        else if turn_a {
            Self::greedy_sum(cnt.update(d, cnt[d] - 1), d, a * 10 + d, b, false)
        } else {
            Self::greedy_sum(cnt.update(d, cnt[d] - 1), d, a, b * 10 + d, true)
        }
    }

    pub open spec fn min_split_sum(num: int) -> int {
        Self::greedy_sum(Self::digit_count_seq(num), 0, 0, 0, true)
    }

    pub fn split_num(num: i32) -> (result: i32)
        requires
            10 <= num <= 1_000_000_000,
        ensures
            result >= 0,
            exists|a: int, b: int|
                #[trigger] Self::valid_split_sum(num as int, a, b)
                && result as int == a + b,
            result as int == Self::min_split_sum(num as int),
    {
    }
}

}
