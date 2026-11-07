use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            s[0] as int + Self::seq_sum(s.subrange(1, s.len() as int))
        }
    }

    pub open spec fn can_partition(rest: Seq<i32>, a: int, b: int, c: int, d: int, target: int) -> bool
        decreases rest.len(),
    {
        if rest.len() == 0 {
            a == target && b == target && c == target && d == target
        } else {
            let x = rest[0] as int;
            ((a + x <= target) && Self::can_partition(rest.subrange(1, rest.len() as int), a + x, b, c, d, target))
            || ((b + x <= target) && Self::can_partition(rest.subrange(1, rest.len() as int), a, b + x, c, d, target))
            || ((c + x <= target) && Self::can_partition(rest.subrange(1, rest.len() as int), a, b, c + x, d, target))
            || ((d + x <= target) && Self::can_partition(rest.subrange(1, rest.len() as int), a, b, c, d + x, target))
        }
    }

    pub open spec fn can_form_square(matchsticks: Seq<i32>) -> bool {
        let total = Self::seq_sum(matchsticks);
        matchsticks.len() >= 4
        && total % 4 == 0
        && Self::can_partition(matchsticks, 0, 0, 0, 0, total / 4)
    }

    pub fn makesquare(matchsticks: Vec<i32>) -> (res: bool)
        requires
            1 <= matchsticks.len() <= 15,
            forall |i: int| 0 <= i < matchsticks.len() ==> 1 <= #[trigger] matchsticks[i] <= 100_000_000,
        ensures
            res == Self::can_form_square(matchsticks@),
    {
    }
}

}
