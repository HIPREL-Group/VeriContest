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

    proof fn lemma_min_assoc(a: int, b: int, c: int)
        ensures
            Self::min2(a, Self::min2(b, c)) == Self::min2(Self::min2(a, b), c),
    {
    }

    proof fn lemma_idx_bound(i: int, j: int, n: int)
        requires 0 <= i < n, 0 <= j < n, n >= 1,
        ensures 0 <= i * n + j < n * n,
    {
        assert(0 <= i * n + j) by (nonlinear_arith) requires 0 <= i, 0 <= j, n >= 1, {}
        assert(i * n + j < n * n) by (nonlinear_arith) requires 0 <= i < n, 0 <= j < n, {}
    }

    proof fn lemma_idx_injective(a: int, b: int, c: int, d: int, n: int)
        requires 0 <= a < n, 0 <= b < n, 0 <= c < n, 0 <= d < n, n >= 1,
                 a * n + b == c * n + d,
        ensures a == c, b == d,
    {
        assert((a - c) * n == d - b) by (nonlinear_arith) requires a * n + b == c * n + d, {}
        assert(-n < d - b < n);
        if a > c {
            assert((a - c) * n >= n) by (nonlinear_arith) requires a > c, n >= 1, {}
        }
        if a < c {
            assert((a - c) * n <= -n) by (nonlinear_arith) requires a < c, n >= 1, {}
        }
    }

    proof fn lemma_min_score_bounds(values: Seq<i32>, i: int, j: int)
        requires
            0 <= i <= j < values.len(), values.len() <= 50,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
        ensures
            j - i < 2 ==> Self::min_score(values, i, j) == 0,
            j - i >= 2 ==> 1 <= Self::min_score(values, i, j) <= (j - i - 1) * 1_000_000,
        decreases j - i,
    {
        if j - i >= 2 {
            Self::lemma_min_score_k_bounds(values, i, j, i + 1);
        }
    }

    proof fn lemma_min_score_k_bounds(values: Seq<i32>, i: int, j: int, k: int)
        requires
            0 <= i, i < k, k <= j, j < values.len(),
            j - i >= 2, values.len() <= 50,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
        ensures
            k < j ==> 1 <= Self::min_score_k(values, i, j, k) <= (j - i - 1) * 1_000_000,
            k >= j ==> Self::min_score_k(values, i, j, k) == i32::MAX as int,
        decreases j - i, j - k,
    {
        if k >= j {
        } else {
            Self::lemma_min_score_bounds(values, i, k);
            Self::lemma_min_score_bounds(values, k, j);
            let left = Self::min_score(values, i, k);
            let right = Self::min_score(values, k, j);
            let vi = values[i] as int;
            let vk = values[k] as int;
            let vj = values[j] as int;
            let product = vi * vk * vj;
            let cur = left + right + product;
            assert(1 <= product <= 1_000_000) by (nonlinear_arith)
                requires 1 <= vi <= 100, 1 <= vk <= 100, 1 <= vj <= 100, product == vi * vk * vj,
            {}
            assert(left >= 0) by { if k - i < 2 { assert(left == 0); } }
            assert(right >= 0) by { if j - k < 2 { assert(right == 0); } }
            assert(cur >= 1);
            assert(left <= (k - i - 1) * 1_000_000) by {
                if k - i < 2 { assert(left == 0); assert(k - i >= 1); }
            }
            assert(right <= (j - k - 1) * 1_000_000) by {
                if j - k < 2 { assert(right == 0); assert(j - k >= 1); }
            }
            assert(cur <= (j - i - 1) * 1_000_000) by (nonlinear_arith)
                requires
                    left <= (k - i - 1) * 1_000_000, right <= (j - k - 1) * 1_000_000,
                    product <= 1_000_000, cur == left + right + product, k - i >= 1, j - k >= 1,
            {}
            if k + 1 < j {
                Self::lemma_min_score_k_bounds(values, i, j, k + 1);
            }
        }
    }

    proof fn lemma_dp_entry_bound(values: Seq<i32>, dp: Seq<i32>, n: int, a: int, b: int)
        requires
            0 <= a < n, 0 <= b < n, n >= 3, n <= 50,
            0 <= a * n + b < n * n,
            dp.len() == n * n, values.len() == n,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
            dp[a * n + b] as int == Self::min_score(values, a, b),
            b >= a,
        ensures
            0 <= dp[a * n + b] as int <= 48_000_000,
    {
        Self::lemma_min_score_bounds(values, a, b);
        if b - a < 2 {
        } else {
            assert(b - a - 1 <= 48);
            assert((b - a - 1) * 1_000_000 <= 48_000_000) by (nonlinear_arith)
                requires b - a - 1 <= 48, {}
        }
    }

    
    proof fn lemma_min_score_k_le_tree(
        values: Seq<i32>, i: int, j: int, k: int,
        tree: SplitTree, k0: int,
        left_tree: SplitTree, right_tree: SplitTree,
    )
        requires
            0 <= i, j < values.len() as int, j - i >= 2, values.len() <= 50,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
            i < k, k <= k0, k0 < j,
            split_tree_valid(left_tree, i, k0),
            split_tree_valid(right_tree, k0, j),
            tree == SplitTree::Node(k0, Box::new(left_tree), Box::new(right_tree)),
            Self::min_score(values, i, k0)
                <= split_tree_score(values, left_tree, i, k0),
            Self::min_score(values, k0, j)
                <= split_tree_score(values, right_tree, k0, j),
        ensures
            Self::min_score_k(values, i, j, k)
                <= split_tree_score(values, tree, i, j),
        decreases j - k,
    {
        let score = split_tree_score(values, tree, i, j);
        let cost_k0 = Self::min_score(values, i, k0)
            + Self::min_score(values, k0, j)
            + values[i] as int * values[k0] as int * values[j] as int;
        assert(score == split_tree_score(values, left_tree, i, k0)
            + values[i] as int * values[k0] as int * values[j] as int
            + split_tree_score(values, right_tree, k0, j));
        assert(score >= cost_k0);
        if k == k0 {
            let mk = Self::min_score_k(values, i, j, k);
            if k + 1 >= j {
                assert(mk == cost_k0);
            } else {
                assert(mk == Self::min2(cost_k0,
                    Self::min_score_k(values, i, j, k + 1)));
                assert(mk <= cost_k0);
            }
        } else {
            Self::lemma_min_score_k_le_tree(
                values, i, j, k + 1, tree, k0, left_tree, right_tree);
            let rest = Self::min_score_k(values, i, j, k + 1);
            let cur_k = Self::min_score(values, i, k) + Self::min_score(values, k, j)
                + values[i] as int * values[k] as int * values[j] as int;
            assert(Self::min_score_k(values, i, j, k) == Self::min2(cur_k, rest));
            assert(Self::min2(cur_k, rest) <= rest);
        }
    }

    
    proof fn lemma_min_score_le_any(
        values: Seq<i32>, i: int, j: int, tree: SplitTree,
    )
        requires
            0 <= i <= j, j < values.len() as int, values.len() <= 50,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
            split_tree_valid(tree, i, j),
        ensures
            Self::min_score(values, i, j) <= split_tree_score(values, tree, i, j),
        decreases j - i,
    {
        match tree {
            SplitTree::Leaf => {
                assert(j - i < 2);
            },
            SplitTree::Node(k0, left_tree, right_tree) => {
                Self::lemma_min_score_le_any(values, i, k0, *left_tree);
                Self::lemma_min_score_le_any(values, k0, j, *right_tree);
                Self::lemma_min_score_k_le_tree(
                    values, i, j, i + 1, tree, k0, *left_tree, *right_tree);
            },
        }
    }

    
    proof fn lemma_min_score_k_achieved(
        values: Seq<i32>, i: int, j: int, k: int,
    ) -> (best_k: int)
        requires
            0 <= i, i < k, k < j, j < values.len() as int,
            j - i >= 2, values.len() <= 50,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
        ensures
            i < best_k < j,
            Self::min_score_k(values, i, j, k) ==
                Self::min_score(values, i, best_k) + Self::min_score(values, best_k, j)
                + values[i] as int * values[best_k] as int * values[j] as int,
        decreases j - k,
    {
        let cur = Self::min_score(values, i, k) + Self::min_score(values, k, j)
            + values[i] as int * values[k] as int * values[j] as int;
        if k + 1 >= j {
            k
        } else {
            let rest = Self::min_score_k(values, i, j, k + 1);
            if cur <= rest {
                k
            } else {
                Self::lemma_min_score_k_achieved(values, i, j, k + 1)
            }
        }
    }

    
    proof fn lemma_min_score_k_val(
        values: Seq<i32>, i: int, j: int, start: int, k0: int,
    )
        requires
            0 <= i, i < start, start <= k0, k0 < j, j < values.len() as int,
            j - i >= 2, values.len() <= 50,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
        ensures
            Self::min_score_k(values, i, j, start) <=
                Self::min_score(values, i, k0) + Self::min_score(values, k0, j)
                + values[i] as int * values[k0] as int * values[j] as int,
        decreases j - start,
    {
        let cur = Self::min_score(values, i, start) + Self::min_score(values, start, j)
            + values[i] as int * values[start] as int * values[j] as int;
        if start == k0 {
            if start + 1 >= j {
            } else {
                assert(Self::min_score_k(values, i, j, start)
                    == Self::min2(cur, Self::min_score_k(values, i, j, start + 1)));
                assert(Self::min2(cur, Self::min_score_k(values, i, j, start + 1)) <= cur);
            }
        } else {
            if start + 1 >= j {
            } else {
                Self::lemma_min_score_k_val(values, i, j, start + 1, k0);
                let rest = Self::min_score_k(values, i, j, start + 1);
                assert(Self::min_score_k(values, i, j, start)
                    == Self::min2(cur, rest));
                assert(Self::min2(cur, rest) <= rest);
            }
        }
    }

    
    proof fn lemma_min_score_achieved(values: Seq<i32>, i: int, j: int)
        -> (tree: SplitTree)
        requires
            0 <= i <= j, j < values.len() as int, values.len() <= 50,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
        ensures
            split_tree_valid(tree, i, j),
            split_tree_score(values, tree, i, j) == Self::min_score(values, i, j),
        decreases j - i,
    {
        if j - i < 2 {
            SplitTree::Leaf
        } else {
            let best_k = Self::lemma_min_score_k_achieved(values, i, j, i + 1);
            let left_tree = Self::lemma_min_score_achieved(values, i, best_k);
            let right_tree = Self::lemma_min_score_achieved(values, best_k, j);
            SplitTree::Node(best_k, Box::new(left_tree), Box::new(right_tree))
        }
    }

    
    proof fn lemma_bridge(values: Seq<i32>)
        requires
            3 <= values.len() <= 50,
            forall|kk: int| 0 <= kk < values.len() ==> 1 <= #[trigger] values[kk] <= 100,
        ensures
            exists|tree: SplitTree|
                #[trigger] split_tree_valid(tree, 0, (values.len() - 1) as int)
                && split_tree_score(values, tree, 0, (values.len() - 1) as int)
                    == Self::min_score(values, 0, (values.len() - 1) as int),
            forall|tree: SplitTree|
                split_tree_valid(tree, 0, (values.len() - 1) as int)
                ==> Self::min_score(values, 0, (values.len() - 1) as int)
                    <= #[trigger] split_tree_score(
                        values, tree, 0, (values.len() - 1) as int),
    {
        let n = values.len() as int;
        let witness = Self::lemma_min_score_achieved(values, 0, n - 1);
        assert(split_tree_valid(witness, 0, n - 1));
        assert(split_tree_score(values, witness, 0, n - 1)
            == Self::min_score(values, 0, n - 1));
        assert forall|tree: SplitTree|
            split_tree_valid(tree, 0, n - 1)
            implies Self::min_score(values, 0, n - 1)
                <= #[trigger] split_tree_score(values, tree, 0, n - 1) by {
            Self::lemma_min_score_le_any(values, 0, n - 1, tree);
        };
    }

    fn triple_product(a: i32, b: i32, c: i32) -> (r: i32)
        requires 1 <= a <= 100, 1 <= b <= 100, 1 <= c <= 100,
        ensures r as int == a as int * b as int * c as int,
                1 <= r <= 1_000_000,
    {
        proof {
            assert(a as int * b as int <= 10000) by (nonlinear_arith)
                requires 1 <= a as int <= 100, 1 <= b as int <= 100, {}
            assert(a as int * b as int >= 1) by (nonlinear_arith)
                requires a as int >= 1, b as int >= 1, {}
        }
        let ab = a * b;
        proof {
            assert(ab as int * c as int <= 1_000_000) by (nonlinear_arith)
                requires 1 <= ab as int <= 10000, 1 <= c as int <= 100, {}
            assert(ab as int * c as int >= 1) by (nonlinear_arith)
                requires ab as int >= 1, c as int >= 1, {}
        }
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
        assert(n * n <= 2500) by (nonlinear_arith) requires 3 <= n <= 50, {}
        let nn = n * n;
        let mut dp: Vec<i32> = Vec::new();
        let mut idx = 0usize;
        while idx < nn
            invariant
                dp@.len() == idx as int, idx <= nn,
                nn == n * n, nn <= 2500, n == values.len(), 3 <= n <= 50,
                forall|i: int| 0 <= i < idx as int ==> dp@[i] == 0i32,
            decreases nn - idx,
        {
            dp.push(0i32);
            idx = idx + 1;
        }
        proof {
            assert forall|ii: int, jj: int|
                0 <= ii < n as int && 0 <= jj < n as int && 0 <= jj - ii < 2
                implies dp@[ii * (n as int) + jj] as int == Self::min_score(values@, ii, jj) by {
                Self::lemma_idx_bound(ii, jj, n as int);
            };
        }
        let mut gap = 2usize;
        while gap < n
            invariant
                dp@.len() == nn as int, nn == n * n, nn <= 2500,
                n == values.len(), 3 <= n <= 50, 2 <= gap <= n,
                forall|ii: int| 0 <= ii < values@.len() ==> 1 <= #[trigger] values@[ii] <= 100,
                forall|ii: int, jj: int|
                    0 <= ii < n as int && 0 <= jj < n as int && 0 <= jj - ii < gap as int
                        ==> dp@[ii * (n as int) + jj] as int == Self::min_score(values@, ii, jj),
            decreases n - gap,
        {
            let mut i = 0usize;
            while i + gap < n
                invariant
                    dp@.len() == nn as int, nn == n * n, nn <= 2500,
                    n == values.len(), 3 <= n <= 50,
                    2 <= gap < n, 0 <= i, i + gap <= n,
                    forall|ii: int| 0 <= ii < values@.len() ==> 1 <= #[trigger] values@[ii] <= 100,
                    forall|ii: int, jj: int|
                        0 <= ii < n as int && 0 <= jj < n as int && 0 <= jj - ii < gap as int
                            ==> dp@[ii * (n as int) + jj] as int == Self::min_score(values@, ii, jj),
                    forall|ii: int|
                        0 <= ii < i as int && ii + (gap as int) < n as int
                            ==> #[trigger] dp@[ii * (n as int) + ii + gap as int] as int
                                == Self::min_score(values@, ii, ii + gap as int),
                decreases n - gap - i,
            {
                let j = i + gap;
                let k_first: usize = i + 1;
                proof {
                    let ii = i as int;
                    let kf = k_first as int;
                    let jj = j as int;
                    let nn_i = n as int;
                    Self::lemma_idx_bound(ii, kf, nn_i);
                    Self::lemma_idx_bound(kf, jj, nn_i);
                    assert(0 <= kf - ii < gap as int);
                    assert(0 <= jj - kf < gap as int);
                    assert(dp@[ii * nn_i + kf] as int == Self::min_score(values@, ii, kf));
                    assert(dp@[kf * nn_i + jj] as int == Self::min_score(values@, kf, jj));
                    Self::lemma_dp_entry_bound(values@, dp@, nn_i, ii, kf);
                    Self::lemma_dp_entry_bound(values@, dp@, nn_i, kf, jj);
                }
                let dl = dp[i * n + k_first];
                let dr = dp[k_first * n + j];
                let prod = Self::triple_product(values[i], values[k_first], values[j]);
                let score_first = dl + dr + prod;
                let mut best: i32 = score_first;
                proof {
                    let ii = i as int;
                    let jj = j as int;
                    let kk = k_first as int;
                    let cur_spec = Self::min_score(values@, ii, kk) + Self::min_score(values@, kk, jj)
                        + values@[ii] as int * values@[kk] as int * values@[jj] as int;
                    assert(best as int == cur_spec);
                    Self::lemma_min_score_k_bounds(values@, ii, jj, ii + 1);
                    Self::lemma_min_score_bounds(values@, ii, jj);
                    assert(1 <= Self::min_score(values@, ii, jj) <= (jj - ii - 1) * 1_000_000);
                    if gap as int == 2 {
                        assert(kk + 1 >= jj);
                        assert(Self::min_score_k(values@, ii, jj, kk) == cur_spec);
                        assert(Self::min_score(values@, ii, jj) == cur_spec);
                        assert(Self::min_score_k(values@, ii, jj, kk + 1) == i32::MAX as int);
                        assert(Self::min_score_k(values@, ii, jj, ii + 1) == Self::min2(
                            best as int, Self::min_score_k(values@, ii, jj, kk + 1)));
                    } else {
                        assert(kk + 1 < jj);
                        assert(Self::min_score_k(values@, ii, jj, kk) == Self::min2(
                            cur_spec, Self::min_score_k(values@, ii, jj, kk + 1)));
                        assert(Self::min_score_k(values@, ii, jj, ii + 1) == Self::min2(
                            best as int, Self::min_score_k(values@, ii, jj, kk + 1)));
                    }
                    Self::lemma_min_score_bounds(values@, ii, kk);
                    Self::lemma_min_score_bounds(values@, kk, jj);
                    let ms_left = Self::min_score(values@, ii, kk);
                    let ms_right = Self::min_score(values@, kk, jj);
                    assert(ms_left == 0);
                    assert(ms_right >= 0) by { if jj - kk < 2 { assert(ms_right == 0); } }
                    assert(ms_right <= (jj - kk - 1) * 1_000_000) by {
                        if jj - kk < 2 { assert(ms_right == 0); assert(jj - kk >= 1); }
                    }
                    assert(1 <= prod as int <= 1_000_000);
                    assert(cur_spec >= 1);
                    assert(cur_spec <= (jj - ii - 1) * 1_000_000) by (nonlinear_arith)
                        requires
                            ms_left == 0, ms_right <= (jj - kk - 1) * 1_000_000,
                            prod as int <= 1_000_000, cur_spec == ms_left + ms_right + prod as int,
                            kk == ii + 1, jj - kk >= 1,
                    {}
                    assert(1 <= best as int <= (jj - ii - 1) * 1_000_000);
                }
                let mut k: usize = i + 2;
                while k < j
                    invariant
                        i + 2 <= k <= j, j == i + gap,
                        2 <= gap < n, dp@.len() == nn as int,
                        nn == n * n, nn <= 2500, n == values.len(), 3 <= n <= 50,
                        0 <= i, i + gap < n,
                        forall|ii: int| 0 <= ii < values@.len() ==> 1 <= #[trigger] values@[ii] <= 100,
                        forall|ii: int, jj: int|
                            0 <= ii < n as int && 0 <= jj < n as int && 0 <= jj - ii < gap as int
                                ==> dp@[ii * (n as int) + jj] as int == Self::min_score(values@, ii, jj),
                        Self::min_score_k(values@, i as int, j as int, i as int + 1)
                            == Self::min2(best as int, Self::min_score_k(values@, i as int, j as int, k as int)),
                        1 <= best as int <= (gap as int - 1) * 1_000_000,
                    decreases j - k,
                {
                    proof {
                        let ii = i as int;
                        let kk = k as int;
                        let jj = j as int;
                        let nn_i = n as int;
                        assert(0 < kk - ii < gap as int);
                        assert(0 < jj - kk < gap as int);
                        Self::lemma_idx_bound(ii, kk, nn_i);
                        Self::lemma_idx_bound(kk, jj, nn_i);
                        assert(dp@[ii * nn_i + kk] as int == Self::min_score(values@, ii, kk));
                        assert(dp@[kk * nn_i + jj] as int == Self::min_score(values@, kk, jj));
                        Self::lemma_dp_entry_bound(values@, dp@, nn_i, ii, kk);
                        Self::lemma_dp_entry_bound(values@, dp@, nn_i, kk, jj);
                    }
                    let dl2 = dp[i * n + k];
                    let dr2 = dp[k * n + j];
                    let prod2 = Self::triple_product(values[i], values[k], values[j]);
                    let score = dl2 + dr2 + prod2;
                    let ghost old_best = best as int;
                    if score < best {
                        best = score;
                    }
                    proof {
                        let ii = i as int;
                        let jj = j as int;
                        let kk = k as int;
                        let new_best = best as int;
                        let cur_spec = Self::min_score(values@, ii, kk) + Self::min_score(values@, kk, jj)
                            + values@[ii] as int * values@[kk] as int * values@[jj] as int;
                        assert(score as int == cur_spec);
                        assert(new_best == Self::min2(old_best, score as int));
                        if kk + 1 < jj {
                            assert(Self::min_score_k(values@, ii, jj, kk) == Self::min2(
                                cur_spec, Self::min_score_k(values@, ii, jj, kk + 1)));
                            Self::lemma_min_assoc(
                                old_best, cur_spec, Self::min_score_k(values@, ii, jj, kk + 1));
                            assert(Self::min_score_k(values@, ii, jj, ii + 1) == Self::min2(
                                new_best, Self::min_score_k(values@, ii, jj, kk + 1)));
                        } else {
                            assert(Self::min_score_k(values@, ii, jj, kk) == cur_spec);
                            assert(Self::min_score_k(values@, ii, jj, kk + 1) == i32::MAX as int);
                            assert(Self::min2(new_best, i32::MAX as int) == new_best);
                        }
                        Self::lemma_min_score_k_bounds(values@, ii, jj, ii + 1);
                        Self::lemma_min_score_bounds(values@, ii, jj);
                    }
                    k = k + 1;
                }
                proof {
                    let ii = i as int;
                    let jj = j as int;
                    assert(k as int == jj);
                    assert(Self::min_score_k(values@, ii, jj, jj) == i32::MAX as int);
                    assert(Self::min2(best as int, i32::MAX as int) == best as int);
                    assert(best as int == Self::min_score(values@, ii, jj));
                    Self::lemma_idx_bound(ii, jj, n as int);
                }
                let ghost old_dp = dp@;
                dp.set(i * n + j, best);
                proof {
                    let ii = i as int;
                    let jj = j as int;
                    let nn_i = n as int;
                    assert forall|a: int, b: int|
                        0 <= a < nn_i && 0 <= b < nn_i && 0 <= b - a < gap as int
                        implies dp@[a * nn_i + b] as int == Self::min_score(values@, a, b) by {
                        Self::lemma_idx_bound(a, b, nn_i);
                        Self::lemma_idx_bound(ii, jj, nn_i);
                        if a * nn_i + b == ii * nn_i + jj {
                            Self::lemma_idx_injective(a, b, ii, jj, nn_i);
                            assert(b - a == gap as int);
                        } else {
                            assert(dp@[a * nn_i + b] == old_dp[a * nn_i + b]);
                        }
                    };
                    assert forall|a: int|
                        0 <= a < ii + 1 && a + (gap as int) < nn_i
                        implies #[trigger] dp@[a * nn_i + a + gap as int] as int
                            == Self::min_score(values@, a, a + gap as int) by {
                        Self::lemma_idx_bound(a, a + gap as int, nn_i);
                        Self::lemma_idx_bound(ii, jj, nn_i);
                        if a == ii {
                            assert(dp@[a * nn_i + a + gap as int] == best);
                        } else {
                            if a * nn_i + a + gap as int == ii * nn_i + jj {
                                Self::lemma_idx_injective(a, a + gap as int, ii, jj, nn_i);
                            } else {
                                assert(dp@[a * nn_i + a + gap as int]
                                    == old_dp[a * nn_i + a + gap as int]);
                            }
                        }
                    };
                }
                i = i + 1;
            }
            proof {
                let nn_i = n as int;
                let gg = gap as int;
                assert forall|ii: int, jj: int|
                    0 <= ii < nn_i && 0 <= jj < nn_i && 0 <= jj - ii < gg + 1
                    implies dp@[ii * nn_i + jj] as int == Self::min_score(values@, ii, jj) by {
                    Self::lemma_idx_bound(ii, jj, nn_i);
                    if jj - ii < gg {} else {
                        assert(jj - ii == gg);
                        assert(jj == ii + gg);
                        assert(ii + gg < nn_i);
                        assert(ii < i as int) by {
                            assert(i + gap >= n);
                            assert(ii + (gap as int) < (n as int));
                        }
                        assert(dp@[ii * (n as int) + ii + gap as int] as int
                            == Self::min_score(values@, ii, ii + gap as int));
                    }
                };
            }
            gap = gap + 1;
        }
        proof {
            let nn_i = n as int;
            assert(nn_i - 1 < gap as int);
            Self::lemma_idx_bound(0, nn_i - 1, nn_i);
            assert(dp@[0 * nn_i + nn_i - 1] as int == Self::min_score(values@, 0, nn_i - 1));
            assert(0 * nn_i == 0) by (nonlinear_arith) {}
            Self::lemma_bridge(values@);
        }
        dp[n - 1]
    }
}

}
