use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_triplets_k(s: Seq<i32>, diff: int, i: int, j: int, k: int) -> int
        decreases s.len() - k
    {
        if k >= s.len() { 0 }
        else {
            (if s[j] as int - s[i] as int == diff && s[k] as int - s[j] as int == diff { 1int } else { 0int })
            + Self::count_triplets_k(s, diff, i, j, k + 1)
        }
    }

    pub open spec fn count_triplets_j(s: Seq<i32>, diff: int, i: int, j: int) -> int
        decreases s.len() - j
    {
        if j >= s.len() { 0 }
        else {
            Self::count_triplets_k(s, diff, i, j, j + 1)
            + Self::count_triplets_j(s, diff, i, j + 1)
        }
    }

    pub open spec fn count_triplets(s: Seq<i32>, diff: int, i: int) -> int
        decreases s.len() - i
    {
        if i >= s.len() { 0 }
        else {
            Self::count_triplets_j(s, diff, i, i + 1)
            + Self::count_triplets(s, diff, i + 1)
        }
    }

    proof fn lemma_count_k_nonneg(s: Seq<i32>, diff: int, i: int, j: int, k: int)
        ensures Self::count_triplets_k(s, diff, i, j, k) >= 0
        decreases s.len() - k
    {
        if k < s.len() as int {
            Self::lemma_count_k_nonneg(s, diff, i, j, k + 1);
        }
    }

    proof fn lemma_count_j_nonneg(s: Seq<i32>, diff: int, i: int, j: int)
        ensures Self::count_triplets_j(s, diff, i, j) >= 0
        decreases s.len() - j
    {
        if j < s.len() as int {
            Self::lemma_count_k_nonneg(s, diff, i, j, j + 1);
            Self::lemma_count_j_nonneg(s, diff, i, j + 1);
        }
    }

    proof fn lemma_count_nonneg(s: Seq<i32>, diff: int, i: int)
        ensures Self::count_triplets(s, diff, i) >= 0
        decreases s.len() - i
    {
        if i < s.len() as int {
            Self::lemma_count_j_nonneg(s, diff, i, i + 1);
            Self::lemma_count_nonneg(s, diff, i + 1);
        }
    }

    proof fn lemma_count_k_upper(s: Seq<i32>, diff: int, i: int, j: int, k: int)
        ensures Self::count_triplets_k(s, diff, i, j, k) <= (if k <= s.len() as int { s.len() - k } else { 0 })
        decreases s.len() - k
    {
        if k < s.len() as int {
            Self::lemma_count_k_upper(s, diff, i, j, k + 1);
        }
    }

    proof fn lemma_count_j_upper(s: Seq<i32>, diff: int, i: int, j: int)
        requires 0 <= j <= s.len() as int
        ensures Self::count_triplets_j(s, diff, i, j) <= (s.len() - j) * s.len()
        decreases s.len() - j
    {
        if j < s.len() as int {
            Self::lemma_count_k_upper(s, diff, i, j, j + 1);
            Self::lemma_count_j_upper(s, diff, i, j + 1);
            let n = s.len() as int;
            assert((n - j - 1) + (n - j - 1) * n <= (n - j) * n) by(nonlinear_arith)
                requires j >= 0, j < n, n >= 0;
        }
    }

    proof fn lemma_count_upper(s: Seq<i32>, diff: int, i: int)
        requires 0 <= i <= s.len() as int
        ensures Self::count_triplets(s, diff, i) <= (s.len() - i) * s.len() * s.len()
        decreases s.len() - i
    {
        if i < s.len() as int {
            Self::lemma_count_j_upper(s, diff, i, i + 1);
            Self::lemma_count_upper(s, diff, i + 1);
            let n = s.len() as int;
            assert((n - i - 1) * n + (n - i - 1) * n * n <= (n - i) * n * n) by(nonlinear_arith)
                requires i >= 0, i < n, n >= 0;
        }
    }

    pub fn arithmetic_triplets(nums: Vec<i32>, diff: i32) -> (result: i32)
        requires
            3 <= nums.len() <= 200,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 200,
            1 <= diff <= 50,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
        ensures
            result as int == Self::count_triplets(nums@, diff as int, 0),
    {
        proof {
            Self::lemma_count_nonneg(nums@, diff as int, 0);
            Self::lemma_count_upper(nums@, diff as int, 0);
            let n = nums.len() as int;
            assert(n * n * n <= 8_000_000) by(nonlinear_arith)
                requires n <= 200, n >= 0;
        }
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() <= 200,
                forall |idx: int| 0 <= idx < nums.len() ==> 0 <= #[trigger] nums[idx] <= 200,
                1 <= diff <= 50,
                forall |a: int, b: int| 0 <= a < b < nums.len() ==> nums[a] < nums[b],
                ans as int == Self::count_triplets(nums@, diff as int, 0) - Self::count_triplets(nums@, diff as int, i as int),
                Self::count_triplets(nums@, diff as int, 0) >= 0,
                Self::count_triplets(nums@, diff as int, 0) <= 8_000_000,
                0 <= ans <= 8_000_000i32,
            decreases nums.len() - i
        {
            proof {
                Self::lemma_count_j_nonneg(nums@, diff as int, i as int, (i + 1) as int);
                Self::lemma_count_nonneg(nums@, diff as int, (i + 1) as int);
                Self::lemma_count_upper(nums@, diff as int, (i + 1) as int);
            }
            let mut j: usize = i + 1;
            while j < nums.len()
                invariant
                    i < nums.len(),
                    i + 1 <= j <= nums.len(),
                    nums.len() <= 200,
                    forall |idx: int| 0 <= idx < nums.len() ==> 0 <= #[trigger] nums[idx] <= 200,
                    1 <= diff <= 50,
                    forall |a: int, b: int| 0 <= a < b < nums.len() ==> nums[a] < nums[b],
                    ans as int == Self::count_triplets(nums@, diff as int, 0) - Self::count_triplets(nums@, diff as int, i as int + 1) - Self::count_triplets_j(nums@, diff as int, i as int, j as int),
                    Self::count_triplets(nums@, diff as int, 0) >= 0,
                    Self::count_triplets(nums@, diff as int, 0) <= 8_000_000,
                    Self::count_triplets(nums@, diff as int, i as int + 1) >= 0,
                    Self::count_triplets_j(nums@, diff as int, i as int, j as int) >= 0,
                    0 <= ans <= 8_000_000i32,
                decreases nums.len() - j
            {
                proof {
                    Self::lemma_count_k_nonneg(nums@, diff as int, i as int, j as int, (j + 1) as int);
                    Self::lemma_count_j_nonneg(nums@, diff as int, i as int, (j + 1) as int);
                    Self::lemma_count_k_upper(nums@, diff as int, i as int, j as int, (j + 1) as int);
                }
                let mut k: usize = j + 1;
                while k < nums.len()
                    invariant
                        j < nums.len(),
                        i < j,
                        i < nums.len(),
                        j + 1 <= k <= nums.len(),
                        nums.len() <= 200,
                        forall |idx: int| 0 <= idx < nums.len() ==> 0 <= #[trigger] nums[idx] <= 200,
                        1 <= diff <= 50,
                        forall |a: int, b: int| 0 <= a < b < nums.len() ==> nums[a] < nums[b],
                        ans as int == Self::count_triplets(nums@, diff as int, 0) - Self::count_triplets(nums@, diff as int, i as int + 1) - Self::count_triplets_j(nums@, diff as int, i as int, j as int + 1) - Self::count_triplets_k(nums@, diff as int, i as int, j as int, k as int),
                        Self::count_triplets(nums@, diff as int, 0) >= 0,
                        Self::count_triplets(nums@, diff as int, 0) <= 8_000_000,
                        Self::count_triplets(nums@, diff as int, i as int + 1) >= 0,
                        Self::count_triplets_j(nums@, diff as int, i as int, j as int + 1) >= 0,
                        Self::count_triplets_k(nums@, diff as int, i as int, j as int, k as int) >= 0,
                        0 <= ans <= 8_000_000i32,
                    decreases nums.len() - k
                {
                    if (nums[j] as i64 - nums[i] as i64) == diff as i64
                        && (nums[k] as i64 - nums[j] as i64) == diff as i64 {
                        proof {
                            Self::lemma_count_k_nonneg(nums@, diff as int, i as int, j as int, (k + 1) as int);
                        }
                        ans = ans + 1;
                    }
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        ans
    }
}

}
