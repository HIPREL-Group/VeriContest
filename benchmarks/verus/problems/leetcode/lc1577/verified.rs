use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn triplet_match(a: Seq<i32>, b: Seq<i32>, i: int, j: int, k: int) -> int {
    if a[i] as int * a[i] as int == b[j] as int * b[k] as int { 1 } else { 0 }
}

pub open spec fn count_k(a: Seq<i32>, b: Seq<i32>, i: int, j: int, k: int) -> int
    decreases b.len() - k
{
    if k >= b.len() { 0 }
    else { triplet_match(a, b, i, j, k) + count_k(a, b, i, j, k + 1) }
}

pub open spec fn count_j(a: Seq<i32>, b: Seq<i32>, i: int, j: int) -> int
    decreases b.len() - j
{
    if j >= b.len() { 0 }
    else { count_k(a, b, i, j, j + 1) + count_j(a, b, i, j + 1) }
}

pub open spec fn count_i(a: Seq<i32>, b: Seq<i32>, i: int) -> int
    decreases a.len() - i
{
    if i >= a.len() { 0 }
    else { count_j(a, b, i, 0) + count_i(a, b, i + 1) }
}

pub open spec fn count_triplets(nums1: Seq<i32>, nums2: Seq<i32>) -> int {
    count_i(nums1, nums2, 0) + count_i(nums2, nums1, 0)
}

proof fn lemma_count_k_bounds(a: Seq<i32>, b: Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= i < a.len(),
        0 <= j < b.len(),
        j + 1 <= k <= b.len(),
    ensures
        0 <= count_k(a, b, i, j, k) <= b.len() - k,
    decreases b.len() - k
{
    if k < b.len() {
        lemma_count_k_bounds(a, b, i, j, k + 1);
    }
}

proof fn lemma_count_j_bounds(a: Seq<i32>, b: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j <= b.len(),
        b.len() <= 1000,
    ensures
        0 <= count_j(a, b, i, j) <= (b.len() - j) * b.len(),
    decreases b.len() - j
{
    if j < b.len() {
        lemma_count_k_bounds(a, b, i, j, j + 1);
        lemma_count_j_bounds(a, b, i, j + 1);
        assert((b.len() - j - 1) + (b.len() - j - 1) * b.len() <= (b.len() - j) * b.len()) by(nonlinear_arith)
            requires 0 <= j < b.len(), b.len() <= 1000;
    }
}

proof fn lemma_count_i_bounds(a: Seq<i32>, b: Seq<i32>, i: int)
    requires
        0 <= i <= a.len(),
        a.len() <= 1000,
        b.len() <= 1000,
    ensures
        0 <= count_i(a, b, i) <= (a.len() - i) * b.len() * b.len(),
    decreases a.len() - i
{
    if i < a.len() {
        lemma_count_j_bounds(a, b, i, 0);
        lemma_count_i_bounds(a, b, i + 1);
        assert(b.len() * b.len() + (a.len() - i - 1) * b.len() * b.len()
            == (a.len() - i) * b.len() * b.len()) by(nonlinear_arith)
            requires a.len() - i >= 1;
    }
}

proof fn lemma_triplets_bound(nums1: Seq<i32>, nums2: Seq<i32>)
    requires
        nums1.len() <= 1000,
        nums2.len() <= 1000,
    ensures
        0 <= count_triplets(nums1, nums2) <= 2_000_000_000,
{
    lemma_count_i_bounds(nums1, nums2, 0);
    lemma_count_i_bounds(nums2, nums1, 0);
    assert(nums1.len() * nums2.len() * nums2.len()
        + nums2.len() * nums1.len() * nums1.len() <= 2_000_000_000) by(nonlinear_arith)
        requires nums1.len() <= 1000, nums2.len() <= 1000;
}

proof fn lemma_count_upper(
    a: Seq<i32>, b: Seq<i32>,
    ii: int, jj: int, kk: int,
)
    requires
        0 <= ii < a.len(),
        0 <= jj < b.len(),
        jj + 1 <= kk <= b.len(),
        a.len() <= 1000,
        b.len() <= 1000,
    ensures
        count_i(a, b, ii + 1) >= 0,
        count_j(a, b, ii, jj + 1) >= 0,
        count_k(a, b, ii, jj, kk) >= 0,
        count_i(a, b, ii) == count_j(a, b, ii, 0) + count_i(a, b, ii + 1),
        count_j(a, b, ii, jj) == count_k(a, b, ii, jj, jj + 1) + count_j(a, b, ii, jj + 1),
{
    lemma_count_i_bounds(a, b, ii + 1);
    lemma_count_j_bounds(a, b, ii, jj + 1);
    lemma_count_k_bounds(a, b, ii, jj, kk);
}

impl Solution {
    pub fn num_triplets(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 100_000,
            forall |i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 100_000,
        ensures
            result as int == count_triplets(nums1@, nums2@),
    {
        proof {
            lemma_triplets_bound(nums1@, nums2@);
        }

        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut count: i32 = 0;

        let mut i: usize = 0;
        while i < n1
            invariant
                0 <= i <= n1,
                n1 == nums1.len(),
                n2 == nums2.len(),
                nums1.len() <= 1000,
                nums2.len() <= 1000,
                forall |idx: int| 0 <= idx < nums1.len() ==> 1 <= #[trigger] nums1[idx] <= 100_000,
                forall |idx: int| 0 <= idx < nums2.len() ==> 1 <= #[trigger] nums2[idx] <= 100_000,
                count as int == count_i(nums1@, nums2@, 0) - count_i(nums1@, nums2@, i as int),
                0 <= count as int <= count_triplets(nums1@, nums2@),
                count_triplets(nums1@, nums2@) <= 2_000_000_000,
            decreases n1 - i,
        {
            let mut j: usize = 0;
            while j < n2
                invariant
                    0 <= i < n1,
                    0 <= j <= n2,
                    n1 == nums1.len(),
                    n2 == nums2.len(),
                    nums1.len() <= 1000,
                    nums2.len() <= 1000,
                    forall |idx: int| 0 <= idx < nums1.len() ==> 1 <= #[trigger] nums1[idx] <= 100_000,
                    forall |idx: int| 0 <= idx < nums2.len() ==> 1 <= #[trigger] nums2[idx] <= 100_000,
                    count as int == count_i(nums1@, nums2@, 0) - count_i(nums1@, nums2@, i as int)
                        + count_j(nums1@, nums2@, i as int, 0)
                        - count_j(nums1@, nums2@, i as int, j as int),
                    0 <= count as int <= count_triplets(nums1@, nums2@),
                    count_triplets(nums1@, nums2@) <= 2_000_000_000,
                decreases n2 - j,
            {
                let mut k: usize = j + 1;
                while k < n2
                    invariant
                        0 <= i < n1,
                        0 <= j < n2,
                        j + 1 <= k <= n2,
                        n1 == nums1.len(),
                        n2 == nums2.len(),
                        nums1.len() <= 1000,
                        nums2.len() <= 1000,
                        forall |idx: int| 0 <= idx < nums1.len() ==> 1 <= #[trigger] nums1[idx] <= 100_000,
                        forall |idx: int| 0 <= idx < nums2.len() ==> 1 <= #[trigger] nums2[idx] <= 100_000,
                        count as int == count_i(nums1@, nums2@, 0) - count_i(nums1@, nums2@, i as int)
                            + count_j(nums1@, nums2@, i as int, 0)
                            - count_j(nums1@, nums2@, i as int, j as int)
                            + count_k(nums1@, nums2@, i as int, j as int, j as int + 1)
                            - count_k(nums1@, nums2@, i as int, j as int, k as int),
                        0 <= count as int <= count_triplets(nums1@, nums2@),
                        count_triplets(nums1@, nums2@) <= 2_000_000_000,
                    decreases n2 - k,
                {
                    proof {
                        let a1 = nums1[i as int] as int;
                        let b1 = nums2[j as int] as int;
                        let b2 = nums2[k as int] as int;
                        assert(a1 * a1 <= 10_000_000_000i64) by(nonlinear_arith)
                            requires 1 <= a1 <= 100_000;
                        assert(b1 * b2 <= 10_000_000_000i64) by(nonlinear_arith)
                            requires 1 <= b1 <= 100_000, 1 <= b2 <= 100_000;
                    }
                    if (nums1[i] as i64) * (nums1[i] as i64) == (nums2[j] as i64) * (nums2[k] as i64) {
                        proof {
                            lemma_count_upper(nums1@, nums2@, i as int, j as int, k as int + 1);
                            lemma_count_i_bounds(nums2@, nums1@, 0);
                        }
                        count = count + 1;
                    }
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }

        let mut i2: usize = 0;
        while i2 < n2
            invariant
                0 <= i2 <= n2,
                n1 == nums1.len(),
                n2 == nums2.len(),
                nums1.len() <= 1000,
                nums2.len() <= 1000,
                forall |idx: int| 0 <= idx < nums1.len() ==> 1 <= #[trigger] nums1[idx] <= 100_000,
                forall |idx: int| 0 <= idx < nums2.len() ==> 1 <= #[trigger] nums2[idx] <= 100_000,
                count as int == count_i(nums1@, nums2@, 0)
                    + count_i(nums2@, nums1@, 0) - count_i(nums2@, nums1@, i2 as int),
                0 <= count as int <= count_triplets(nums1@, nums2@),
                count_triplets(nums1@, nums2@) <= 2_000_000_000,
            decreases n2 - i2,
        {
            let mut j2: usize = 0;
            while j2 < n1
                invariant
                    0 <= i2 < n2,
                    0 <= j2 <= n1,
                    n1 == nums1.len(),
                    n2 == nums2.len(),
                    nums1.len() <= 1000,
                    nums2.len() <= 1000,
                    forall |idx: int| 0 <= idx < nums1.len() ==> 1 <= #[trigger] nums1[idx] <= 100_000,
                    forall |idx: int| 0 <= idx < nums2.len() ==> 1 <= #[trigger] nums2[idx] <= 100_000,
                    count as int == count_i(nums1@, nums2@, 0)
                        + count_i(nums2@, nums1@, 0) - count_i(nums2@, nums1@, i2 as int)
                        + count_j(nums2@, nums1@, i2 as int, 0)
                        - count_j(nums2@, nums1@, i2 as int, j2 as int),
                    0 <= count as int <= count_triplets(nums1@, nums2@),
                    count_triplets(nums1@, nums2@) <= 2_000_000_000,
                decreases n1 - j2,
            {
                let mut k2: usize = j2 + 1;
                while k2 < n1
                    invariant
                        0 <= i2 < n2,
                        0 <= j2 < n1,
                        j2 + 1 <= k2 <= n1,
                        n1 == nums1.len(),
                        n2 == nums2.len(),
                        nums1.len() <= 1000,
                        nums2.len() <= 1000,
                        forall |idx: int| 0 <= idx < nums1.len() ==> 1 <= #[trigger] nums1[idx] <= 100_000,
                        forall |idx: int| 0 <= idx < nums2.len() ==> 1 <= #[trigger] nums2[idx] <= 100_000,
                        count as int == count_i(nums1@, nums2@, 0)
                            + count_i(nums2@, nums1@, 0) - count_i(nums2@, nums1@, i2 as int)
                            + count_j(nums2@, nums1@, i2 as int, 0)
                            - count_j(nums2@, nums1@, i2 as int, j2 as int)
                            + count_k(nums2@, nums1@, i2 as int, j2 as int, j2 as int + 1)
                            - count_k(nums2@, nums1@, i2 as int, j2 as int, k2 as int),
                        0 <= count as int <= count_triplets(nums1@, nums2@),
                        count_triplets(nums1@, nums2@) <= 2_000_000_000,
                    decreases n1 - k2,
                {
                    proof {
                        let a2 = nums2[i2 as int] as int;
                        let c1 = nums1[j2 as int] as int;
                        let c2 = nums1[k2 as int] as int;
                        assert(a2 * a2 <= 10_000_000_000i64) by(nonlinear_arith)
                            requires 1 <= a2 <= 100_000;
                        assert(c1 * c2 <= 10_000_000_000i64) by(nonlinear_arith)
                            requires 1 <= c1 <= 100_000, 1 <= c2 <= 100_000;
                    }
                    if (nums2[i2] as i64) * (nums2[i2] as i64) == (nums1[j2] as i64) * (nums1[k2] as i64) {
                        proof {
                            lemma_count_upper(nums2@, nums1@, i2 as int, j2 as int, k2 as int + 1);
                            lemma_count_i_bounds(nums1@, nums2@, 0);
                        }
                        count = count + 1;
                    }
                    k2 = k2 + 1;
                }
                j2 = j2 + 1;
            }
            i2 = i2 + 1;
        }

        count
    }
}

}
