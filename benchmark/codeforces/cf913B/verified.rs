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
        while i < n 
            invariant
                0 <= i && i <= n,
                is_p.len() == i,
                forall|j: int| 0 <= j && j < i ==> is_p@[j] == false,
            decreases n - i
        {
            is_p.push(false);
            i += 1;
        }

        i = 0;
        while i < p.len()
            invariant
                0 <= i && i <= p.len(),
                n <= 1000,
                n == is_p.len(),
                p.len() == n - 1,
                forall|j: int| 0 <= j && j < p.len() ==> p@[j] <= j as usize,
                forall|v: int| 0 <= v && v < n ==> 
                    is_p@[v] == exists|k: int| 0 <= k && k < i && p@[k] == v as usize,
            decreases p.len() - i
        {
            let parent = p[i];
            is_p.set(parent, true);
            
            proof {
                assert forall|v: int| 0 <= v && v < n implies
                    is_p@[v] == exists|k: int| 0 <= k && k < i + 1 && p@[k] == v as usize
                by {
                    if v == parent as int {
                        assert(0 <= i && i < i + 1);
                        assert(p@[i as int] == v as usize);
                    } else {
                        if exists|k: int| 0 <= k && k < i + 1 && p@[k] == v as usize {
                            let k_witness = choose|k: int| 0 <= k && k < i + 1 && p@[k] == v as usize;
                            assert(k_witness != i as int);
                            assert(0 <= k_witness && k_witness < i);
                        }
                    }
                }
            }
            
            i += 1;
        }

        let mut leaf_children_count = Vec::new();
        let mut j = 0;
        while j < n
            invariant
                0 <= j && j <= n,
                n <= 1000,
                n == is_p.len(),
                p.len() == n - 1,
                leaf_children_count.len() == j,
                forall|v: int| 0 <= v && v < j ==> leaf_children_count@[v] == 0int,
            decreases n - j
        {
            leaf_children_count.push(0);
            j += 1;
        }

        j = 0;
        while j < p.len()
            invariant
                0 <= j && j <= p.len(),
                n <= 1000,
                n == is_p.len(),
                n == leaf_children_count.len(),
                p.len() == n - 1,
                forall|k: int| 0 <= k && k < p.len() ==> p@[k] <= k as usize,
                forall|v: int| 0 <= v && v < n ==> 
                    is_p@[v] == is_parent(p@, v as usize),
                forall|v: int| 0 <= v && v < n ==>
                    leaf_children_count@[v] == num_leaf_children(p@, v as usize, j as int),
                forall|v: int| 0 <= v && v < n ==>
                    leaf_children_count@[v] <= j as usize,
            decreases p.len() - j
        {
            let is_leaf_node = !is_p[j + 1];
            if is_leaf_node {
                let parent = p[j];
                let cnt = leaf_children_count[parent];
                leaf_children_count.set(parent, cnt + 1);
            }
            
            proof {
                assert forall|v: int| 0 <= v && v < n implies
                    leaf_children_count@[v] == num_leaf_children(p@, v as usize, j as int + 1)
                by {
                    assert(num_leaf_children(p@, v as usize, j as int + 1) == 
                           num_leaf_children(p@, v as usize, j as int) + 
                           if p@[j as int] == v as usize && is_leaf(p@, (j + 1) as usize) { 1int } else { 0int });
                }
            }
            
            j += 1;
        }

        let mut k = 0;
        let mut ans = true;
        while k < n
            invariant
                0 <= k && k <= n,
                n <= 1000,
                n == is_p.len(),
                n == leaf_children_count.len(),
                p.len() == n - 1,
                forall|v: int| 0 <= v && v < n ==> 
                    is_p@[v] == is_parent(p@, v as usize),
                forall|v: int| 0 <= v && v < n ==>
                    leaf_children_count@[v] == num_leaf_children(p@, v as usize, p.len() as int),
                ans == forall|v: int| 0 <= v && v < k ==>
                    (#[trigger] is_parent(p@, v as usize) ==> num_leaf_children(p@, v as usize, p.len() as int) >= 3),
            decreases n - k
        {
            if is_p[k] && leaf_children_count[k] < 3 {
                ans = false;
            }
            k += 1;
        }

        ans
    }
}

}
