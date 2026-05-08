use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn can_make_same_parity_spec(s: Seq<i64>) -> bool {
    (forall|i: int|
        0 <= i < s.len() && i % 2 == 0
            ==> ((#[trigger] s[i] as int) % 2 == (s[0] as int) % 2))
    &&
    (s.len() < 2 || forall|i: int|
        0 <= i < s.len() && i % 2 == 1
            ==> ((#[trigger] s[i] as int) % 2 == (s[1] as int) % 2))
}

impl Solution {
    pub fn can_make_same_parity(a: Vec<i64>) -> (res: bool)
        requires
            1 <= a.len() <= 50,
            forall|k: int| 0 <= k < a.len() as int ==> 1 <= #[trigger] a[k] as int <= 1000,
        ensures
            res == can_make_same_parity_spec(a@),
    {
        let n = a.len();
        let mut i: usize = 0;
        while i < n {
            if a[i] % 2 != a[0] % 2 {
                return false;
            }
            i = i + 2;
        }

        if n >= 2 {
            let mut j: usize = 1;
            while j < n {
                if a[j] % 2 != a[1] % 2 {
                    return false;
                }
                j = j + 2;
            }
        }

        true
    }
}

}