use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_eq_prefix(a: Seq<i32>, i: int, v: i32) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        count_eq_prefix(a, i - 1, v) + (if a[i - 1] == v { 1int } else { 0int })
    }
}

pub open spec fn fair_division_possible(a: Seq<i32>, n: int) -> bool {
    let c1 = count_eq_prefix(a, n, 1);
    let c2 = count_eq_prefix(a, n, 2);
    let total = c1 + 2 * c2;
    total % 2 == 0
        && exists|m: int|
            0 <= m && m <= c2 && 0 <= #[trigger] (total / 2 - 2 * m) && total / 2 - 2 * m <= c1
}

pub struct Solution;

impl Solution {
    pub fn fair_division(n: usize, a: Vec<i32>) -> (res: bool)
        requires
            1 <= n <= 100,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> (a@[i] == 1 || a@[i] == 2),
        ensures
            res == fair_division_possible(a@, n as int),
    {
        let mut c1: i32 = 0;
        let mut c2: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 1 {
                c1 = c1 + 1;
            } else {
                c2 = c2 + 1;
            }
            i = i + 1;
        }
        let total = c1 + 2 * c2;
        if total % 2 != 0 {
            return false;
        }
        let half = total / 2;
        let mut m: i32 = 0;
        while m <= c2 {
            let n1 = half - 2 * m;
            if n1 >= 0 && n1 <= c1 {
                return true;
            }
            m = m + 1;
        }
        false
    }
}

}
