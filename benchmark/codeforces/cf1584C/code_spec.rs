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
        let n = a.len();
        let mut carry: i64 = 0;
        let mut val: i32 = -100;

        while val <= 100 {
            let mut av: usize = 0;
            let mut vi: usize = 0;
            while vi < n {
                if a[vi] == val {
                    av = av + 1;
                }
                vi = vi + 1;
            }

            let mut bv: usize = 0;
            vi = 0;
            while vi < n {
                if b[vi] == val {
                    bv = bv + 1;
                }
                vi = vi + 1;
            }

            let next = av as i64 - bv as i64 + carry;
            if next < 0 || next > av as i64 {
                return false;
            }

            carry = next;
            val = val + 1;
        }

        carry == 0
    }
}

}
