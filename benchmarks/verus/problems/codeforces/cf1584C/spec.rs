use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_value_prefix(s: Seq<i32>, val: int, upto: nat) -> int
    recommends
        upto <= s.len(),
    decreases
        upto,
{
    if upto == 0 {
        0
    } else {
        let prev = (upto as int - 1) as nat;
        count_value_prefix(s, val, prev) + if s[prev as int] as int == val { 1int } else { 0int }
    }
}

pub open spec fn count_value(s: Seq<i32>, val: int) -> int {
    count_value_prefix(s, val, s.len())
}

pub open spec fn feasible_from_value(a: Seq<i32>, b: Seq<i32>, val: int, carry: int) -> bool
    recommends
        a.len() == b.len(),
        -100 <= val <= 101,
        0 <= carry,
    decreases
        101 - val,
{
    if val > 100 {
        carry == 0
    } else {
        let av = count_value(a, val);
        let bv = count_value(b, val);
        let next = av - bv + carry;
        0 <= next <= av && feasible_from_value(a, b, val + 1, next)
    }
}

pub struct Solution;

impl Solution {
    pub fn can_transform(a: Vec<i32>, b: Vec<i32>) -> (ok: bool)
        requires
            1 <= a.len() <= 100,
            a.len() == b.len(),
            forall|i: int| 0 <= i < a.len() ==> -100 <= #[trigger] a[i] <= 100,
            forall|i: int| 0 <= i < b.len() ==> -100 <= #[trigger] b[i] <= 100,
        ensures
            ok == feasible_from_value(a@, b@, -100, 0),
    {
    }
}

}
