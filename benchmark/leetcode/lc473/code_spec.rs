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
        if matchsticks.len() < 4 {
            return false;
        }
        let total = Self::sum_from(&matchsticks, 0);
        if total % 4 != 0 {
            return false;
        }
        Self::search(&matchsticks, 0, 0, 0, 0, 0, total / 4)
    }

    fn sum_from(matchsticks: &Vec<i32>, index: usize) -> (total: i32)
        requires
            index <= matchsticks.len(),
            matchsticks.len() <= 21,
            forall |i: int| 0 <= i < matchsticks.len() ==> 1 <= #[trigger] matchsticks[i] <= 100_000_000,
        ensures
            total as int == Self::seq_sum(matchsticks@.subrange(index as int, matchsticks.len() as int)),
            0 <= total as int <= (matchsticks.len() as int - index as int) * 100_000_000,
        decreases matchsticks.len() - index,
    {
        if index == matchsticks.len() {
            0
        } else {
            let rest = Self::sum_from(matchsticks, index + 1);
            matchsticks[index] + rest
        }
    }

    fn search(matchsticks: &Vec<i32>, index: usize, side0: i32, side1: i32, side2: i32, side3: i32, target: i32) -> (res: bool)
        requires
            index <= matchsticks.len(),
            0 <= target,
            0 <= side0 <= target,
            0 <= side1 <= target,
            0 <= side2 <= target,
            0 <= side3 <= target,
            forall |i: int| 0 <= i < matchsticks.len() ==> 1 <= #[trigger] matchsticks[i] <= 100_000_000,
        ensures
            res == Self::can_partition(matchsticks@.subrange(index as int, matchsticks.len() as int), side0 as int, side1 as int, side2 as int, side3 as int, target as int),
        decreases matchsticks.len() - index,
    {
        if index == matchsticks.len() {
            return side0 == target && side1 == target && side2 == target && side3 == target;
        }
        let x = matchsticks[index];
        let found0 = if x <= target - side0 {
            let r = Self::search(matchsticks, index + 1, side0 + x, side1, side2, side3, target);
            if r {
                return true;
            }
            r
        } else {
            false
        };
        let found1 = if side1 != side0 && x <= target - side1 {
            let r = Self::search(matchsticks, index + 1, side0, side1 + x, side2, side3, target);
            if r {
                return true;
            }
            r
        } else {
            false
        };
        let found2 = if side2 != side0 && side2 != side1 && x <= target - side2 {
            let r = Self::search(matchsticks, index + 1, side0, side1, side2 + x, side3, target);
            if r {
                return true;
            }
            r
        } else {
            false
        };
        let found3 = if side3 != side0 && side3 != side1 && side3 != side2 && x <= target - side3 {
            let r = Self::search(matchsticks, index + 1, side0, side1, side2, side3 + x, target);
            if r {
                return true;
            }
            r
        } else {
            false
        };
        false
    }
}

}
