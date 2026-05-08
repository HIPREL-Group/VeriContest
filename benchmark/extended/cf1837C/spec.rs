use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn best_binary_string(s: Vec<i64>) -> (result: Vec<i64>)
        requires
            s.len() >= 1,
            forall|i: int| 0 <= i < s.len() ==> (#[trigger] s@[i] == 0 || s@[i] == 1 || s@[i] == 2),
        ensures
            result@.len() == s@.len(),
            forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i] == 0 || result@[i] == 1),
            forall|i: int| 0 <= i < s@.len() && s@[i] != 2 ==> #[trigger] result@[i] == s@[i],
            forall|i: int| 0 <= i < s@.len() && s@[i] == 2 ==>
                #[trigger] result@[i] == if i == 0 { 0 } else { result@[i - 1] },
    {
    }
}

}
