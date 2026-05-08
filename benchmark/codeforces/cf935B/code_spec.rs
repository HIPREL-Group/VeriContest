use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn x_pos(s: Seq<i32>, k: int) -> int
    decreases k
{
    if k <= 0 { 0int }
    else { x_pos(s, k - 1) + if s[k - 1] == 1 { 1int } else { 0int } }
}

pub open spec fn y_pos(s: Seq<i32>, k: int) -> int
    decreases k
{
    if k <= 0 { 0int }
    else { y_pos(s, k - 1) + if s[k - 1] == 0 { 1int } else { 0int } }
}

pub open spec fn is_crossing(s: Seq<i32>, k: int) -> bool {
    0 < k && k < s.len() && x_pos(s, k) == y_pos(s, k) && s[k - 1] == s[k]
}

pub open spec fn num_crossings(s: Seq<i32>, k: int) -> int
    decreases k
{
    if k <= 0 { 0int }
    else {
        num_crossings(s, k - 1) + if is_crossing(s, k - 1) { 1int } else { 0int }
    }
}

pub struct Solution;

impl Solution {
    pub fn fafa_and_gates(n: usize, s: Vec<i32>) -> (result: i32)
        requires
            n == s.len(),
            n > 0,
            n <= 100000,
            forall|j: int| 0 <= j && j < n ==> s@[j] == 0 || s@[j] == 1,
        ensures
            result as int == num_crossings(s@, n as int),
    {
        let mut x = 0;
        let mut y = 0;
        let mut coins = 0;
        let mut i = 0;

        while i < n {
            let nxt = s[i];
            if i > 0 && x == y && s[i - 1] == nxt {
                coins += 1;
            }
            if nxt == 1 {
                x += 1;
            } else {
                y += 1;
            }
            i += 1;
        }

        coins
    }
}

}
