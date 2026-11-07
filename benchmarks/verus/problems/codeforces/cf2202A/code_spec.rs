use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn parkour_reachable_spec(x: int, y: int) -> bool {
        exists|a: int, b: int, c: int|
            0 <= a && 0 <= b && 0 <= c
            && #[trigger] (2 * a + 3 * b + 4 * c) == x
            && a - c == y
    }

    pub fn parkour_reachable(x: i64, y: i64) -> (result: bool)
        requires
            1 <= x as int <= 1_000_000_000,
            -100_000_000 <= y as int <= 100_000_000,
        ensures
            result == Self::parkour_reachable_spec(x as int, y as int),
    {
        let diff = x - 2 * y;
        if diff % 3 != 0 {
            return false;
        }
        let m = diff / 3;
        if m < 0 {
            return false;
        }
        let need = if y >= 0 { 0i64 } else { -y };
        need <= m / 2
    }
}

}
