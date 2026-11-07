use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff_digits(a: int, b: int) -> int {
    if a <= b {
        b - a
    } else {
        a - b
    }
}

pub open spec fn digit_circular_moves(a: int, b: int) -> int {
    let d = abs_diff_digits(a, b);
    if d <= 5 {
        d
    } else {
        10 - d
    }
}

pub open spec fn sum_lock_moves(init: Seq<u8>, goal: Seq<u8>, end: int) -> int
    recommends
        init.len() == goal.len(),
        0 <= end <= init.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        let prev = end - 1;
        sum_lock_moves(init, goal, prev)
            + digit_circular_moves(init[prev] as int, goal[prev] as int)
    }
}

impl Solution {
    pub fn min_lock_moves(n: usize, current: Vec<u8>, target: Vec<u8>) -> (result: u32)
        requires
            1 <= n <= 1000,
            current.len() == n,
            target.len() == n,
            forall |i: int|
                0 <= i < n as int ==> 0 <= #[trigger] current[i] <= 9,
            forall |i: int|
                0 <= i < n as int ==> 0 <= #[trigger] target[i] <= 9,
        ensures
            result as int == sum_lock_moves(current@, target@, n as int),
    {
    }
}

}
