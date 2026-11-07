use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() == v { 1int } else { 0int }) + Self::count(s.drop_last(), v)
        }
    }

    pub fn can_be_equal(target: Vec<i32>, arr: Vec<i32>) -> (res: bool)
        requires
            target.len() == arr.len(),
            1 <= target.len() <= 1000,
            forall |i: int| 0 <= i < target.len() ==> 1 <= #[trigger] target[i] <= 1000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
        ensures
            res == (forall |v: i32| Self::count(target@, v) == Self::count(arr@, v)),
    {
    }
}

}
