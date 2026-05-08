use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_triples_k(s: Seq<i32>, i: int, j: int, k: int) -> int
        decreases s.len() - k
    {
        if k >= s.len() { 0 }
        else {
            (if s[i] != s[j] && s[i] != s[k] && s[j] != s[k] { 1int } else { 0int })
            + Self::count_triples_k(s, i, j, k + 1)
        }
    }

    pub open spec fn count_triples_j(s: Seq<i32>, i: int, j: int) -> int
        decreases s.len() - j
    {
        if j >= s.len() { 0 }
        else {
            Self::count_triples_k(s, i, j, j + 1) + Self::count_triples_j(s, i, j + 1)
        }
    }

    pub open spec fn count_triples_i(s: Seq<i32>, i: int) -> int
        decreases s.len() - i
    {
        if i >= s.len() { 0 }
        else {
            Self::count_triples_j(s, i, i + 1) + Self::count_triples_i(s, i + 1)
        }
    }

    proof fn lemma_count_triples_k_bound(s: Seq<i32>, i: int, j: int, k: int)
        ensures
            0 <= Self::count_triples_k(s, i, j, k),
            Self::count_triples_k(s, i, j, k) <= if k < s.len() { s.len() - k } else { 0 },
        decreases s.len() - k
    {
        if k < s.len() {
            Self::lemma_count_triples_k_bound(s, i, j, k + 1);
        }
    }

    proof fn lemma_count_triples_j_bound(s: Seq<i32>, i: int, j: int)
        ensures
            0 <= Self::count_triples_j(s, i, j),
            Self::count_triples_j(s, i, j) <= if j < s.len() { (s.len() - j) * (s.len() - j) } else { 0 },
        decreases s.len() - j
    {
        if j < s.len() {
            Self::lemma_count_triples_k_bound(s, i, j, j + 1);
            Self::lemma_count_triples_j_bound(s, i, j + 1);
            let n = s.len();
            assert((n - j - 1) + (n - j - 1) * (n - j - 1) <= (n - j) * (n - j)) by (nonlinear_arith)
                requires n - j >= 1;
        }
    }

    proof fn lemma_count_triples_i_bound(s: Seq<i32>, i: int)
        ensures
            0 <= Self::count_triples_i(s, i),
            Self::count_triples_i(s, i) <= if i < s.len() { (s.len() - i) * (s.len() - i) * (s.len() - i) } else { 0 },
        decreases s.len() - i
    {
        if i < s.len() {
            Self::lemma_count_triples_j_bound(s, i, i + 1);
            Self::lemma_count_triples_i_bound(s, i + 1);
            let n = s.len();
            assert((n - i - 1) * (n - i - 1) + (n - i - 1) * (n - i - 1) * (n - i - 1)
                <= (n - i) * (n - i) * (n - i)) by (nonlinear_arith)
                requires n - i >= 1;
        }
    }

    pub fn unequal_triplets(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::count_triples_i(nums@, 0),
    {
        let n = nums.len();
        if n < 3 {
            return 0;
        }

        proof {
            Self::lemma_count_triples_i_bound(nums@, 0);
            assert((n as int) * (n as int) * (n as int) <= 1_000_000int) by (nonlinear_arith)
                requires n as int <= 100, n as int >= 0;
        }

        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n - 2
            invariant
                0 <= i <= n - 2,
                n == nums.len(),
                n >= 3,
                n <= 100,
                ans as int == Self::count_triples_i(nums@, 0) - Self::count_triples_i(nums@, i as int),
                0 <= ans <= 1_000_000,
                Self::count_triples_i(nums@, 0) <= 1_000_000,
            decreases n - 2 - i,
        {
            proof {
                Self::lemma_count_triples_j_bound(nums@, i as int, (i + 1) as int);
                Self::lemma_count_triples_i_bound(nums@, (i + 1) as int);
            }
            let mut j: usize = i + 1;
            while j < n - 1
                invariant
                    i + 1 <= j <= n - 1,
                    n == nums.len(),
                    n >= 3,
                    n <= 100,
                    i < n - 2,
                    ans as int == Self::count_triples_i(nums@, 0) - Self::count_triples_i(nums@, (i + 1) as int) - Self::count_triples_j(nums@, i as int, j as int),
                    0 <= ans <= 1_000_000,
                    Self::count_triples_i(nums@, 0) <= 1_000_000,
                    Self::count_triples_i(nums@, (i + 1) as int) >= 0,
                    Self::count_triples_j(nums@, i as int, j as int) >= 0,
                decreases n - 1 - j,
            {
                proof {
                    Self::lemma_count_triples_k_bound(nums@, i as int, j as int, (j + 1) as int);
                    Self::lemma_count_triples_j_bound(nums@, i as int, (j + 1) as int);
                }
                let mut k: usize = j + 1;
                while k < n
                    invariant
                        j + 1 <= k <= n,
                        n == nums.len(),
                        n >= 3,
                        n <= 100,
                        i < n - 2,
                        j < n - 1,
                        i < j,
                        ans as int == Self::count_triples_i(nums@, 0) - Self::count_triples_i(nums@, (i + 1) as int) - Self::count_triples_j(nums@, i as int, (j + 1) as int) - Self::count_triples_k(nums@, i as int, j as int, k as int),
                        0 <= ans <= 1_000_000,
                        Self::count_triples_i(nums@, 0) <= 1_000_000,
                        Self::count_triples_i(nums@, (i + 1) as int) >= 0,
                        Self::count_triples_j(nums@, i as int, (j + 1) as int) >= 0,
                        Self::count_triples_k(nums@, i as int, j as int, k as int) >= 0,
                    decreases n - k,
                {
                    proof {
                        Self::lemma_count_triples_k_bound(nums@, i as int, j as int, (k + 1) as int);
                    }
                    if nums[i] != nums[j] && nums[i] != nums[k] && nums[j] != nums[k] {
                        ans = ans + 1;
                    }
                    k = k + 1;
                }
                j = j + 1;
            }
            proof {
                assert(Self::count_triples_k(nums@, i as int, (n - 1) as int, n as int) == 0);
                assert(Self::count_triples_j(nums@, i as int, n as int) == 0);
                assert(Self::count_triples_j(nums@, i as int, (n - 1) as int) == 0);
            }
            i = i + 1;
        }
        proof {
            assert(Self::count_triples_k(nums@, (n - 2) as int, (n - 1) as int, n as int) == 0);
            assert(Self::count_triples_j(nums@, (n - 2) as int, n as int) == 0);
            assert(Self::count_triples_j(nums@, (n - 2) as int, (n - 1) as int) == 0);
            assert(Self::count_triples_j(nums@, (n - 1) as int, n as int) == 0);
            assert(Self::count_triples_i(nums@, n as int) == 0);
            assert(Self::count_triples_i(nums@, (n - 1) as int) == 0);
            assert(Self::count_triples_i(nums@, (n - 2) as int) == 0);
        }
        ans
    }
}

}
