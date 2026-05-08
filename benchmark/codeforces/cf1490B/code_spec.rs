use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn rem3(x: i32) -> int {
    let m = x as int % 3;
    if m < 0 {
        m + 3
    } else {
        m
    }
}

pub open spec fn count_rem_prefix(a: Seq<i32>, r: int, idx: int) -> int
    decreases idx,
{
    if idx <= 0 {
        0
    } else {
        (if rem3(a[idx - 1]) == r {
            1int
        } else {
            0int
        }) + count_rem_prefix(a, r, idx - 1)
    }
}

pub open spec fn count_rem(a: Seq<i32>, r: int) -> int {
    count_rem_prefix(a, r, a.len() as int)
}

pub open spec fn min_balance_ops_f(c0: int, c1: int, c2: int, tgt: int, fuel: nat) -> int
    recommends
        c0 + c1 + c2 == 3 * tgt,
    decreases fuel,
{
    if c0 == tgt && c1 == tgt && c2 == tgt {
        0
    } else if fuel == 0 {
        0
    } else if c0 > tgt {
        1 + min_balance_ops_f(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat)
    } else if c1 > tgt {
        1 + min_balance_ops_f(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat)
    } else {
        1 + min_balance_ops_f(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat)
    }
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn min_moves_balance_remainders(a: Vec<i32>) -> (result: i32)
        requires
            3 <= a.len() && a.len() <= 30_000,
            a.len() % 3 == 0,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 100,
        ensures
            result == min_balance_ops_f(
                count_rem(a@, 0),
                count_rem(a@, 1),
                count_rem(a@, 2),
                (a.len() / 3) as int,
                (a.len() * 3) as nat,
            ),
    {
        let n = a.len();
        let tgt = n / 3;
        let mut c0: usize = 0;
        let mut c1: usize = 0;
        let mut c2: usize = 0;
        let mut i: usize = 0;
        while i < n {
            let r = a[i] % 3;
            if r == 0 {
                c0 = c0 + 1;
            } else if r == 1 {
                c1 = c1 + 1;
            } else {
                c2 = c2 + 1;
            }
            i = i + 1;
        }
        let mut ops: usize = 0;
        let total3: usize = n * 3;
        #[verifier::loop_isolation(false)]
        while (c0 != tgt || c1 != tgt || c2 != tgt) && ops < total3 {
            if c0 > tgt {
                c0 = c0 - 1;
                c1 = c1 + 1;
                ops = ops + 1;
            } else if c1 > tgt {
                c1 = c1 - 1;
                c2 = c2 + 1;
                ops = ops + 1;
            } else {
                c2 = c2 - 1;
                c0 = c0 + 1;
                ops = ops + 1;
            }
        }
        ops as i32
    }
}

}
