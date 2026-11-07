use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn product_val(nums: Seq<i32>, i: int, j: int) -> int {
        (nums[i] - 1) * (nums[j] - 1)
    }

    pub fn max_product(nums: Vec<i32>) -> (res: i32)
        requires
            2 <= nums.len() <= 500,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            exists |i: int, j: int| 0 <= i < j < nums.len()
                && res == Self::product_val(nums@, i, j),
            forall |i: int, j: int| 0 <= i < j < nums.len()
                ==> Self::product_val(nums@, i, j) <= res,
    {
        let n = nums.len();
        let mut best: i32;

        proof {
            assert(1 <= nums[0int] <= 1000);
            assert(1 <= nums[1int] <= 1000);
            assert(0 <= (nums[0int] - 1) * (nums[1int] - 1) <= 999 * 999) by(nonlinear_arith)
                requires
                    0 <= nums[0int] - 1 <= 999,
                    0 <= nums[1int] - 1 <= 999,
            {}
        }

        best = (nums[0] - 1) * (nums[1] - 1);

        let ghost mut best_i: int = 0;
        let ghost mut best_j: int = 1;

        let mut i: usize = 0;
        while i < n
            invariant
                2 <= nums.len() <= 500,
                n == nums.len(),
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                0 <= i <= n,
                0 <= best <= 999 * 999,
                0 <= best_i < best_j < nums.len() as int,
                best == Self::product_val(nums@, best_i, best_j),
                forall |a: int, b: int| 0 <= a < i && a < b < nums.len() ==>
                    Self::product_val(nums@, a, b) <= best,
            decreases n - i,
        {
            let mut j: usize = i + 1;
            while j < n
                invariant
                    2 <= nums.len() <= 500,
                    n == nums.len(),
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                    0 <= i < n,
                    i + 1 <= j <= n,
                    0 <= best <= 999 * 999,
                    0 <= best_i < best_j < nums.len() as int,
                    best == Self::product_val(nums@, best_i, best_j),
                    forall |a: int, b: int| 0 <= a < i && a < b < nums.len() ==>
                        Self::product_val(nums@, a, b) <= best,
                    forall |b: int| i < b < j ==>
                        Self::product_val(nums@, i as int, b) <= best,
                decreases n - j,
            {
                proof {
                    assert(0 <= (nums[i as int] - 1) * (nums[j as int] - 1) <= 999 * 999) by(nonlinear_arith)
                        requires
                            0 <= nums[i as int] - 1 <= 999,
                            0 <= nums[j as int] - 1 <= 999,
                    {}
                }
                let prod = (nums[i] - 1) * (nums[j] - 1);
                if prod > best {
                    best = prod;
                    proof {
                        best_i = i as int;
                        best_j = j as int;
                    }
                }
                j += 1;
            }
            i += 1;
        }
        best
    }
}

} 
