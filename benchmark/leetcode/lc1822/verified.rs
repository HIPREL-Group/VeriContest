use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sign_func(x: int) -> int {
    if x > 0 {
        1int
    } else if x < 0 {
        -1int
    } else {
        0int
    }
}

pub open spec fn product_sign(nums: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        1int
    } else {
        sign_func(nums[i - 1] as int) * product_sign(nums, i - 1)
    }
}

proof fn lemma_product_sign_range(nums: Seq<i32>, i: int)
    requires
        0 <= i <= nums.len(),
    ensures
        product_sign(nums, i) == -1
        || product_sign(nums, i) == 0
        || product_sign(nums, i) == 1,
    decreases i,
{
    if i <= 0 {
    } else {
        lemma_product_sign_range(nums, i - 1);
        let s = sign_func(nums[i - 1] as int);
        let p = product_sign(nums, i - 1);
        assert(s == -1 || s == 0 || s == 1);
        assert(p == -1 || p == 0 || p == 1);
        
    }
}

proof fn lemma_sign_zero_absorbs(s: int, p: int)
    requires
        s == 0 || p == 0,
    ensures
        s * p == 0,
{}

proof fn lemma_sign_mul(s: int, p: int)
    requires
        (s == -1 || s == 0 || s == 1),
        (p == -1 || p == 0 || p == 1),
    ensures
        s * p == -1 || s * p == 0 || s * p == 1,
        s == 0 ==> s * p == 0,
        p == 0 ==> s * p == 0,
        (s == 1 && p == 1) ==> s * p == 1,
        (s == -1 && p == -1) ==> s * p == 1,
        (s == 1 && p == -1) ==> s * p == -1,
        (s == -1 && p == 1) ==> s * p == -1,
{}

impl Solution {
    pub fn array_sign(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            res == product_sign(nums@, nums.len() as int),
    {
        let n = nums.len();
        let mut sign: i32 = 1;
        let mut i: usize = 0;

        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> -100 <= #[trigger] nums[k] <= 100,
                0 <= i <= n,
                sign == product_sign(nums@, i as int),
                sign == -1 || sign == 0 || sign == 1,
            decreases n - i,
        {
            proof {
                
                assert(product_sign(nums@, (i + 1) as int)
                    == sign_func(nums[i as int] as int) * product_sign(nums@, i as int));
                lemma_product_sign_range(nums@, i as int);
            }

            if nums[i] == 0 {
                proof {
                    assert(sign_func(nums[i as int] as int) == 0);
                    lemma_sign_mul(0, sign as int);
                }
                sign = 0;
            } else if nums[i] < 0 {
                proof {
                    assert(sign_func(nums[i as int] as int) == -1int);
                    lemma_sign_mul(-1, sign as int);
                }
                sign = sign * -1;
            } else {
                proof {
                    assert(sign_func(nums[i as int] as int) == 1);
                    lemma_sign_mul(1, sign as int);
                }
            }

            proof {
                lemma_product_sign_range(nums@, (i + 1) as int);
            }

            i += 1;
        }

        sign
    }
}

} 
