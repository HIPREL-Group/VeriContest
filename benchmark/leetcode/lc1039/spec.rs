use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;





pub enum SplitTree {
    Leaf,
    Node(int, Box<SplitTree>, Box<SplitTree>),
}



pub open spec fn split_tree_valid(tree: SplitTree, i: int, j: int) -> bool
    decreases tree,
{
    match tree {
        SplitTree::Leaf => j - i < 2,
        SplitTree::Node(k, left, right) =>
            j - i >= 2 && i < k < j
            && split_tree_valid(*left, i, k)
            && split_tree_valid(*right, k, j),
    }
}



pub open spec fn split_tree_score(
    values: Seq<i32>, tree: SplitTree, i: int, j: int,
) -> int
    decreases tree,
{
    match tree {
        SplitTree::Leaf => 0,
        SplitTree::Node(k, left, right) =>
            split_tree_score(values, *left, i, k)
            + values[i] as int * values[k] as int * values[j] as int
            + split_tree_score(values, *right, k, j),
    }
}

impl Solution {
    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn min_score(values: Seq<i32>, i: int, j: int) -> int
        decreases j - i, j - i,
    {
        if j - i < 2 {
            0
        } else {
            Self::min_score_k(values, i, j, i + 1)
        }
    }

    pub open spec fn min_score_k(values: Seq<i32>, i: int, j: int, k: int) -> int
        decreases j - i, j - k,
    {
        if k >= j || k <= i || j - i < 2 {
            i32::MAX as int
        } else {
            let cur = Self::min_score(values, i, k) + Self::min_score(values, k, j)
                + values[i] as int * values[k] as int * values[j] as int;
            if k + 1 >= j {
                cur
            } else {
                Self::min2(cur, Self::min_score_k(values, i, j, k + 1))
            }
        }
    }

    pub fn min_score_triangulation(values: Vec<i32>) -> (res: i32)
        requires
            3 <= values.len() <= 50,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
        ensures
            exists|tree: SplitTree|
                #[trigger] split_tree_valid(tree, 0, (values.len() - 1) as int)
                && split_tree_score(values@, tree, 0, (values.len() - 1) as int) == res as int,
            forall|tree: SplitTree|
                split_tree_valid(tree, 0, (values.len() - 1) as int)
                ==> res as int <= #[trigger] split_tree_score(
                    values@, tree, 0, (values.len() - 1) as int),
    {
    }
}

}
