use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_val(x: i64, y: i64) -> int {
        if x == y { 0 } else { 1 }
    }

    pub open spec fn spec_flip(v: i64) -> i64 {
        (1 - (v as int)) as i64
    }

    pub open spec fn apply_op(a: Seq<i64>, b: Seq<i64>, lo: int, hi: int) -> (Seq<i64>, Seq<i64>) {
        (
            Seq::new(a.len(), |i: int| if lo <= i <= hi { Self::spec_flip(a[i]) } else { a[i] }),
            Seq::new(b.len(), |i: int| if lo <= i <= hi { b[i] } else { Self::spec_flip(b[i]) }),
        )
    }

    pub open spec fn apply_ops(a: Seq<i64>, b: Seq<i64>, ops: Seq<(int, int)>) -> (Seq<i64>, Seq<i64>)
        decreases ops.len(),
    {
        if ops.len() == 0 {
            (a, b)
        } else {
            let prev = Self::apply_ops(a, b, ops.drop_last());
            Self::apply_op(prev.0, prev.1, ops.last().0, ops.last().1)
        }
    }

    pub open spec fn zero_seq(n: nat) -> Seq<i64> {
        Seq::new(n, |i: int| 0i64)
    }

    pub open spec fn to_int_ops(ops: Seq<(usize, usize)>) -> Seq<(int, int)> {
        Seq::new(ops.len(), |k: int| ((ops[k].0 - 1) as int, (ops[k].1 - 1) as int))
    }

    pub fn complementary_xor_ops(a: Vec<i64>, b: Vec<i64>) -> (result: (bool, Vec<(usize, usize)>))
        requires
            a.len() == b.len(),
            2 <= a.len() && a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> (#[trigger] a@[i] == 0 || a@[i] == 1),
            forall|i: int| 0 <= i < b.len() ==> (#[trigger] b@[i] == 0 || b@[i] == 1),
        ensures
            result.0 == (forall|i: int| 0 <= i < a@.len() ==>
                Self::xor_val(#[trigger] a@[i], b@[i]) == Self::xor_val(a@[0], b@[0])),
            !result.0 ==> result.1.len() == 0,
            result.0 ==> {
                &&& result.1.len() <= a.len() + 5
                &&& forall|j: int| 0 <= j < result.1@.len() ==>
                        1 <= #[trigger] result.1@[j].0 <= result.1@[j].1 <= a.len()
                &&& Self::apply_ops(a@, b@, Self::to_int_ops(result.1@))
                        == (Self::zero_seq(a.len() as nat), Self::zero_seq(a.len() as nat))
            },
    {
    }
}

}
