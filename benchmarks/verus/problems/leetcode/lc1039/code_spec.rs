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

    fn triple_product(a: i32, b: i32, c: i32) -> (r: i32)
        requires 1 <= a <= 100, 1 <= b <= 100, 1 <= c <= 100,
        ensures r as int == a as int * b as int * c as int,
                1 <= r <= 1_000_000,
    {
        let ab = a * b;
        ab * c
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
        let n = values.len();
        let nn = n * n;
        let mut dp: Vec<i32> = Vec::new();
        let mut idx = 0usize;
        while idx < nn {
            dp.push(0i32);
            idx = idx + 1;
        }
        let mut gap = 2usize;
        while gap < n {
            let mut i = 0usize;
            while i + gap < n {
                let j = i + gap;
                let k_first: usize = i + 1;
                let dl = dp[i * n + k_first];
                let dr = dp[k_first * n + j];
                let prod = Self::triple_product(values[i], values[k_first], values[j]);
                let score_first = dl + dr + prod;
                let mut best: i32 = score_first;
                let mut k: usize = i + 2;
                while k < j {
                    let dl2 = dp[i * n + k];
                    let dr2 = dp[k * n + j];
                    let prod2 = Self::triple_product(values[i], values[k], values[j]);
                    let score = dl2 + dr2 + prod2;
                    if score < best {
                        best = score;
                    }
                    k = k + 1;
                }
                dp.set(i * n + j, best);
                i = i + 1;
            }
            gap = gap + 1;
        }
        dp[n - 1]
    }
}

}
