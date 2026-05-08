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
        let mut is_p = Vec::new();
        let mut i = 0;
        while i < n {
            is_p.push(false);
            i += 1;
        }

        i = 0;
        while i < p.len() {
            let parent = p[i];
            is_p.set(parent, true);
            i += 1;
        }

        let mut leaf_children_count = Vec::new();
        let mut j = 0;
        while j < n {
            leaf_children_count.push(0);
            j += 1;
        }

        j = 0;
        while j < p.len() {
            let is_leaf_node = !is_p[j + 1];
            if is_leaf_node {
                let parent = p[j];
                let cnt = leaf_children_count[parent];
                leaf_children_count.set(parent, cnt + 1);
            }
            j += 1;
        }

        let mut k = 0;
        let mut ans = true;
        while k < n {
            if is_p[k] && leaf_children_count[k] < 3 {
                ans = false;
            }
            k += 1;
        }

        ans
    }
}

}
