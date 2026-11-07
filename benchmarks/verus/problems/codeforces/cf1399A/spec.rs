use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn same_multiset(left: Seq<i32>, right: Seq<i32>) -> bool {
    left.len() == right.len() && left.to_multiset() =~= right.to_multiset()
}

pub open spec fn sorted_adjacent_steps_at_most_one(s: Seq<i32>, n: int) -> bool {
    n <= s.len()
        && forall|i: int|
            0 <= i < n - 1 ==> {
                &&& #[trigger] s[i] <= s[i + 1]
                &&& (s[i + 1] as int - s[i] as int) <= 1
            }
}

pub open spec fn spec_remove_smallest_possible(a: Seq<i32>) -> bool {
    a.len() >= 1 && exists|s: Seq<i32>|
        s.len() == a.len() && same_multiset(s, a)
            && sorted_adjacent_steps_at_most_one(s, a.len() as int)
}

impl Solution {
    pub fn remove_smallest_possible(a: Vec<i32>) -> (res: bool)
        requires
            1 <= a.len() <= 50,
            forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] as int <= 100,
        ensures
            res == spec_remove_smallest_possible(a@),
    {
    }
}

}
