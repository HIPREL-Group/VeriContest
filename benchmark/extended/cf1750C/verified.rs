use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_val(x: i64, y: i64) -> int {
        if x == y { 0 } else { 1 }
    }

    pub fn is_complementary_xor_possible(a: Vec<i64>, b: Vec<i64>) -> (result: bool)
        requires
            a.len() == b.len(),
            a.len() >= 1,
            forall|i: int| 0 <= i < a.len() ==> (#[trigger] a@[i] == 0 || a@[i] == 1),
            forall|i: int| 0 <= i < b.len() ==> (#[trigger] b@[i] == 0 || b@[i] == 1),
        ensures
            result == (forall|i: int| 0 <= i < a@.len() ==>
                Self::xor_val(#[trigger] a@[i], b@[i]) == Self::xor_val(a@[0], b@[0])),
    {
        let n = a.len();
        let first_xor = if a[0] == b[0] { 0i64 } else { 1i64 };
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == a.len(),
                n == b.len(),
                n >= 1,
                forall|j: int| 0 <= j < a.len() ==> (#[trigger] a@[j] == 0 || a@[j] == 1),
                forall|j: int| 0 <= j < b.len() ==> (#[trigger] b@[j] == 0 || b@[j] == 1),
                first_xor as int == Self::xor_val(a@[0], b@[0]),
                forall|j: int| 0 <= j < i as int ==>
                    Self::xor_val(#[trigger] a@[j], b@[j]) == Self::xor_val(a@[0], b@[0]),
            decreases n - i,
        {
            let cur_xor = if a[i] == b[i] { 0i64 } else { 1i64 };
            if cur_xor != first_xor {
                proof {
                    assert(Self::xor_val(a@[i as int], b@[i as int]) != Self::xor_val(a@[0], b@[0]));
                }
                return false;
            }
            proof {
                assert(Self::xor_val(a@[i as int], b@[i as int]) == Self::xor_val(a@[0], b@[0]));
            }
            i = i + 1;
        }
        true
    }
}

}
