use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_xor(nums: Seq<i32>, len: int) -> i32
    decreases len,
{
    if len <= 0 {
        0i32
    } else {
        prefix_xor(nums, len - 1) ^ nums[len - 1]
    }
}

pub open spec fn mask_for(mb: i32) -> i32 {
    !(!0i32 << (mb as u32))
}

proof fn prefix_xor_remove_last(nums: Seq<i32>, k: int)
    requires
        0 < k <= nums.len(),
    ensures
        prefix_xor(nums, k) ^ nums[k - 1] == prefix_xor(nums, k - 1),
{
    let a = prefix_xor(nums, k - 1);
    let b = nums[k - 1];
    assert((a ^ b) ^ b == a) by(bit_vector);
}

proof fn prefix_xor_bounded(nums: Seq<i32>, k: int, mb: i32)
    requires
        0 <= k <= nums.len(),
        1 <= mb <= 20,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= mask_for(mb),
    ensures
        0 <= prefix_xor(nums, k) <= mask_for(mb),
    decreases k,
{
    let m = mask_for(mb);
    if k <= 0 {
        assert(0i32 <= !(!0i32 << (mb as u32))) by(bit_vector)
            requires 1 <= mb <= 20;
    } else {
        prefix_xor_bounded(nums, k - 1, mb);
        let a = prefix_xor(nums, k - 1);
        let b = nums[k - 1];
        assert(0 <= (a ^ b) && (a ^ b) <= m) by(bit_vector)
            requires
                0 <= a <= m,
                0 <= b <= m,
                1 <= mb <= 20,
                m == !(!0i32 << (mb as u32));
    }
}

proof fn xor_mask_bounded(a: i32, mb: i32)
    requires
        1 <= mb <= 20,
        0 <= a <= mask_for(mb),
    ensures
        0 <= (a ^ mask_for(mb)) <= mask_for(mb),
{
    let m = mask_for(mb);
    assert(0 <= (a ^ m) && (a ^ m) <= m) by(bit_vector)
        requires
            0 <= a <= m,
            1 <= mb <= 20,
            m == !(!0i32 << (mb as u32));
}

proof fn mask_nonneg(mb: i32)
    requires
        1 <= mb <= 20,
    ensures
        mask_for(mb) >= 0i32,
{
    assert(!(!0i32 << (mb as u32)) >= 0i32) by(bit_vector)
        requires 1 <= mb <= 20;
}

impl Solution {
    pub fn get_maximum_xor(nums: Vec<i32>, maximum_bit: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100_000,
            1 <= maximum_bit <= 20,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= mask_for(maximum_bit),
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() ==>
                0 <= #[trigger] result[i] <= mask_for(maximum_bit),
            forall |i: int| 0 <= i < result.len() ==>
                prefix_xor(nums@, (nums@.len() - i) as int) ^ #[trigger] result[i]
                    == mask_for(maximum_bit),
    {
        proof { mask_nonneg(maximum_bit); }

        let mask = !(!0i32 << (maximum_bit as u32));
        let n = nums.len();

        let mut xor_all: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                mask == mask_for(maximum_bit),
                1 <= maximum_bit <= 20,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= mask_for(maximum_bit),
                xor_all == prefix_xor(nums@, i as int),
                0 <= xor_all <= mask_for(maximum_bit),
            decreases n - i,
        {
            proof {
                prefix_xor_bounded(nums@, (i + 1) as int, maximum_bit);
            }
            xor_all = xor_all ^ nums[i];
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == nums.len(),
                mask == mask_for(maximum_bit),
                1 <= maximum_bit <= 20,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= mask_for(maximum_bit),
                xor_all == prefix_xor(nums@, (n - j) as int),
                0 <= xor_all <= mask_for(maximum_bit),
                result.len() == j,
                forall |k: int| 0 <= k < j ==>
                    0 <= #[trigger] result[k] <= mask_for(maximum_bit),
                forall |k: int| 0 <= k < j ==>
                    prefix_xor(nums@, (n - k) as int) ^ #[trigger] result[k]
                        == mask_for(maximum_bit),
            decreases n - j,
        {
            proof {
                xor_mask_bounded(xor_all, maximum_bit);
            }
            let ghost pxor = prefix_xor(nums@, (n - j) as int);
            result.push(xor_all ^ mask);
            proof {
                assert(pxor ^ (pxor ^ mask) == mask) by(bit_vector);
                assert(prefix_xor(nums@, (n - j) as int) ^ result@[j as int]
                    == mask_for(maximum_bit));
                prefix_xor_remove_last(nums@, (n - j) as int);
                prefix_xor_bounded(nums@, (n - j - 1) as int, maximum_bit);
            }
            xor_all = xor_all ^ nums[n - 1 - j];
            j = j + 1;
        }

        result
    }
}

}
