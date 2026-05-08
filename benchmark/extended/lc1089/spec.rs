use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn dup_prefix_capped(s: Seq<i32>, end: int, n: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            Seq::<i32>::empty()
        } else {
            let prev = Self::dup_prefix_capped(s, end - 1, n);
            if prev.len() >= n {
                prev
            } else if s[end - 1] == 0 {
                if prev.len() + 2 <= n {
                    prev + seq![0, 0]
                } else {
                    prev + seq![0]
                }
            } else {
                prev + seq![s[end - 1]]
            }
        }
    }

    pub open spec fn duplicate_zeros_spec(s: Seq<i32>) -> Seq<i32> {
        Self::dup_prefix_capped(s, s.len() as int, s.len() as int)
    }

    pub fn duplicate_zeros(arr: &mut Vec<i32>)
        requires
            1 <= old(arr).len() <= 10_000,
            forall |i: int| 0 <= i < old(arr).len() ==> 0 <= #[trigger] old(arr)[i] <= 9,
        ensures
            arr.len() == old(arr).len(),
            arr@ == Self::duplicate_zeros_spec(old(arr)@),
    {

    }
}

}
