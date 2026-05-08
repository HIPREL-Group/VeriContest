use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_parent(p: Seq<usize>, v: usize) -> bool {
    exists|i: int| 0 <= i && i < p.len() && p[i] == v
}

pub open spec fn is_leaf(p: Seq<usize>, v: usize) -> bool {
    !is_parent(p, v)
}

pub open spec fn num_leaf_children(p: Seq<usize>, v: usize, k: int) -> int
    decreases k
{
    if k <= 0 { 0int }
    else {
        num_leaf_children(p, v, k - 1) +
        if p[k - 1] == v && is_leaf(p, k as usize) { 1int } else { 0int }
    }
}

pub open spec fn is_spruce_tree(p: Seq<usize>, n: usize) -> bool {
    forall|v: int| 0 <= v && v < n ==>
        (#[trigger] is_parent(p, v as usize) ==> num_leaf_children(p, v as usize, p.len() as int) >= 3)
}

pub struct Solution;

impl Solution {
    pub fn is_spruce(n: usize, p: Vec<usize>) -> (result: bool)
        requires
            n >= 3,
            n <= 1000,
            p.len() == n - 1,
            forall|i: int| 0 <= i && i < p.len() ==> p@[i] <= i as usize,
        ensures
            result == is_spruce_tree(p@, n),
    {
    }
}

}
