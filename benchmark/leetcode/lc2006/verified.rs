use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff_is_k(a: i32, b: i32, k: i32) -> bool {
        a - b == k || b - a == k
    }

    pub open spec fn count_pairs_from(nums: Seq<i32>, k: i32, i: int, j: int) -> int
        decreases nums.len() - i, nums.len() - j
    {
        if i >= nums.len() {
            0
        } else if j >= nums.len() {
            Self::count_pairs_from(nums, k, i + 1, i + 2)
        } else {
            (if Self::abs_diff_is_k(nums[i], nums[j], k) { 1int } else { 0int })
                + Self::count_pairs_from(nums, k, i, j + 1)
        }
    }

    proof fn count_pairs_from_nonneg(nums: Seq<i32>, k: i32, i: int, j: int)
        ensures
            Self::count_pairs_from(nums, k, i, j) >= 0,
        decreases nums.len() - i, nums.len() - j
    {
        if i >= nums.len() {
        } else if j >= nums.len() {
            Self::count_pairs_from_nonneg(nums, k, i + 1, i + 2);
        } else {
            Self::count_pairs_from_nonneg(nums, k, i, j + 1);
        }
    }

    proof fn count_pairs_from_bound(nums: Seq<i32>, k: i32, i: int, j: int)
        requires
            0 <= i < nums.len(),
            i + 1 <= j <= nums.len(),
            nums.len() <= 200,
        ensures
            Self::count_pairs_from(nums, k, i, j) <= (nums.len() - i) * nums.len() - (j - i - 1),
        decreases nums.len() - i, nums.len() - j,
    {
        let n = nums.len();
        if j >= n {
            if i + 1 < n {
                Self::count_pairs_from_bound(nums, k, i + 1, i + 2);
                
                
                
                assert((n - i - 1) * n <= (n - i) * n - (n - i - 1)) by(nonlinear_arith)
                    requires n >= 1, 0 <= i, i + 1 < n;
            } else {
                
                assert(Self::count_pairs_from(nums, k, i + 1, i + 2) == 0int);
            }
        } else {
            Self::count_pairs_from_bound(nums, k, i, j + 1);
            
            
            
            Self::count_pairs_from_nonneg(nums, k, i, j + 1);
            assert(Self::count_pairs_from(nums, k, i, j) <=
                1 + Self::count_pairs_from(nums, k, i, j + 1));
        }
    }

    pub fn count_k_difference(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 200,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 99,
        ensures
            result == Self::count_pairs_from(nums@, k, 0, 1),
    {
        let n = nums.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;

        proof {
            Self::count_pairs_from_nonneg(nums@, k, 0int, 1int);
            Self::count_pairs_from_bound(nums@, k, 0int, 1int);
            let sn = nums@.len();
            assert(sn * sn <= 40000) by(nonlinear_arith)
                requires sn <= 200;
        }

        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= nums.len() <= 200,
                forall |idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 100,
                1 <= k <= 99,
                0 <= count <= 40000,
                count == Self::count_pairs_from(nums@, k, 0, 1) - Self::count_pairs_from(nums@, k, i as int, (i + 1) as int),
                0 <= Self::count_pairs_from(nums@, k, 0, 1) <= 40000,
            decreases n - i,
        {
            let mut j: usize = i + 1;

            proof {
                Self::count_pairs_from_nonneg(nums@, k, i as int, (i + 1) as int);
            }

            while j < n
                invariant
                    0 <= i < n,
                    i + 1 <= j <= n,
                    n == nums.len(),
                    1 <= nums.len() <= 200,
                    forall |idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 100,
                    1 <= k <= 99,
                    0 <= count <= 40000,
                    count == Self::count_pairs_from(nums@, k, 0, 1) - Self::count_pairs_from(nums@, k, i as int, j as int),
                    0 <= Self::count_pairs_from(nums@, k, 0, 1) <= 40000,
                    Self::count_pairs_from(nums@, k, i as int, j as int) >= 0,
                decreases n - j,
            {
                proof {
                    Self::count_pairs_from_nonneg(nums@, k, i as int, (j + 1) as int);
                }
                let diff = nums[i] - nums[j];
                if diff == k || diff == -k {
                    count = count + 1;
                }
                j = j + 1;
            }

            proof {
                Self::count_pairs_from_nonneg(nums@, k, (i + 1) as int, (i + 2) as int);
            }

            i = i + 1;
        }
        count
    }
}

}
