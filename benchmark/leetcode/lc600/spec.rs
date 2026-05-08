use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn fibv(bits: int) -> int
        recommends 0 <= bits <= 30
    {
        if bits == 0 { 1 }
        else if bits == 1 { 2 }
        else if bits == 2 { 3 }
        else if bits == 3 { 5 }
        else if bits == 4 { 8 }
        else if bits == 5 { 13 }
        else if bits == 6 { 21 }
        else if bits == 7 { 34 }
        else if bits == 8 { 55 }
        else if bits == 9 { 89 }
        else if bits == 10 { 144 }
        else if bits == 11 { 233 }
        else if bits == 12 { 377 }
        else if bits == 13 { 610 }
        else if bits == 14 { 987 }
        else if bits == 15 { 1597 }
        else if bits == 16 { 2584 }
        else if bits == 17 { 4181 }
        else if bits == 18 { 6765 }
        else if bits == 19 { 10946 }
        else if bits == 20 { 17711 }
        else if bits == 21 { 28657 }
        else if bits == 22 { 46368 }
        else if bits == 23 { 75025 }
        else if bits == 24 { 121393 }
        else if bits == 25 { 196418 }
        else if bits == 26 { 317811 }
        else if bits == 27 { 514229 }
        else if bits == 28 { 832040 }
        else if bits == 29 { 1346269 }
        else { 2178309 }
    }

    pub open spec fn solve_from(n: i64, idx: int, prev_one: bool, acc: int) -> int
        recommends -1 <= idx <= 30
        decreases if idx < 0 { 0int } else { idx as int + 1 }
    {
        if idx < 0 {
            acc + 1
        } else {
            let bit = ((n >> (idx as i32)) & 1) == 1;
            if bit {
                let acc2 = acc + Self::fibv(idx);
                if prev_one {
                    acc2
                } else {
                    Self::solve_from(n, idx - 1, true, acc2)
                }
            } else {
                Self::solve_from(n, idx - 1, false, acc)
            }
        }
    }

    pub open spec fn answer(n: i64) -> int
    {
        Self::solve_from(n, 30, false, 0)
    }

    pub fn find_integers(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000000000,
        ensures
            result as int == Self::answer(n as i64),
    {
    }
}

}
