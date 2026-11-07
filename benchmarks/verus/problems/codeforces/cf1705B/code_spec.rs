use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_ops_suffix(s: Seq<i64>, i: int, started: bool) -> int
    recommends
        0 <= i <= s.len(),
    decreases s.len() - i,
{
    if i >= s.len() - 1 {
        0int
    } else {
        let ai = s[i] as int;
        if ai > 0 {
            ai + spec_ops_suffix(s, i + 1, true)
        } else if started {
            1int + spec_ops_suffix(s, i + 1, true)
        } else {
            spec_ops_suffix(s, i + 1, false)
        }
    }
}

pub open spec fn spec_min_operations(s: Seq<i64>) -> int
    recommends
        s.len() >= 2,
{
    spec_ops_suffix(s, 0, false)
}

impl Solution {
    pub fn min_operations(a: Vec<i64>) -> (res: i64)
        requires
            2 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() as int ==> 0 <= #[trigger] a[j] as int <= 1000000000,
        ensures
            res as int == spec_min_operations(a@),
    {
        let n = a.len();
        let mut ans: i64 = 0;
        let mut started: bool = false;
        let mut i: usize = 0;
        while i + 1 < n {
            let ai = a[i];
            if ai > 0 {
                ans = ans + ai;
                started = true;
            } else if started {
                ans = ans + 1;
            }
            i = i + 1;
        }
        ans
    }
}

}
