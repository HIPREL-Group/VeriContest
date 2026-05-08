use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn matches_rot0(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int) -> bool {
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            mat[i]@[j] == target[i]@[j]
    }

    pub open spec fn matches_rot90(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int) -> bool {
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            mat[i]@[j] == target[j]@[n - 1 - i]
    }

    pub open spec fn matches_rot180(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int) -> bool {
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            mat[i]@[j] == target[n - 1 - i]@[n - 1 - j]
    }

    pub open spec fn matches_rot270(mat: Seq<Vec<i32>>, target: Seq<Vec<i32>>, n: int) -> bool {
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            mat[i]@[j] == target[n - 1 - j]@[i]
    }

    pub fn find_rotation(mat: Vec<Vec<i32>>, target: Vec<Vec<i32>>) -> (result: bool)
        requires
            1 <= mat@.len() <= 10,
            mat@.len() == target@.len(),
            forall |i: int| 0 <= i < mat@.len() ==> (#[trigger] mat@[i])@.len() == mat@.len(),
            forall |i: int| 0 <= i < target@.len() ==> (#[trigger] target@[i])@.len() == target@.len(),
            forall |i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==>
                (mat@[i]@[j] == 0 || mat@[i]@[j] == 1),
            forall |i: int, j: int| 0 <= i < target@.len() && 0 <= j < target@.len() ==>
                (target@[i]@[j] == 0 || target@[i]@[j] == 1),
        ensures
            result == (
                Self::matches_rot0(mat@, target@, mat@.len() as int) ||
                Self::matches_rot90(mat@, target@, mat@.len() as int) ||
                Self::matches_rot180(mat@, target@, mat@.len() as int) ||
                Self::matches_rot270(mat@, target@, mat@.len() as int)
            ),
    {
    }
}

}
