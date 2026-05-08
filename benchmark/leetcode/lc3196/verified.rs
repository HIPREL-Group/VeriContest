use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn i128_min() -> int {
        -170141183460469231731687303715884105728
    }

    pub open spec fn i128_max() -> int {
        170141183460469231731687303715884105727
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn checked_add_or(a: int, b: int, fallback: int) -> int {
        let s = a + b;
        if Self::i128_min() <= s <= Self::i128_max() { s } else { fallback }
    }

    pub open spec fn checked_sub_or(a: int, b: int, fallback: int) -> int {
        let s = a - b;
        if Self::i128_min() <= s <= Self::i128_max() { s } else { fallback }
    }

    pub open spec fn add_state(nums: Seq<i32>, len: int) -> int
        decreases if len > 0 { len } else { 0 },
    {
        if nums.len() == 0 || len <= 0 {
            0
        } else if len == 1 {
            nums[0] as int
        } else {
            Self::checked_add_or(
                Self::max2(Self::add_state(nums, len - 1), Self::sub_state(nums, len - 1)),
                nums[len - 1] as int,
                Self::max2(Self::add_state(nums, len - 1), Self::sub_state(nums, len - 1)),
            )
        }
    }

    pub open spec fn sub_state(nums: Seq<i32>, len: int) -> int
        decreases if len > 0 { len } else { 0 },
    {
        if nums.len() == 0 || len <= 0 {
            0
        } else if len == 1 {
            nums[0] as int
        } else {
            Self::checked_sub_or(
                Self::add_state(nums, len - 1),
                nums[len - 1] as int,
                Self::add_state(nums, len - 1),
            )
        }
    }

    pub open spec fn maximum_total_cost_spec(nums: Seq<i32>, result: int) -> bool {
        &&& 1 <= nums.len() <= 100000
        &&& forall |i: int| 0 <= i < nums.len() ==> -1000000000 <= #[trigger] nums[i] <= 1000000000
        &&& result == (Self::max2(Self::add_state(nums, nums.len() as int), Self::sub_state(nums, nums.len() as int)) as i64) as int
    }

    pub fn maximum_total_cost(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> -1000000000 <= #[trigger] nums[i] <= 1000000000,
        ensures
            Self::maximum_total_cost_spec(nums@, result as int),
    {
        let n = nums.len();
        let mut add_result = nums[0] as i128;
        let mut sub_result = nums[0] as i128;
        let mut i = 1usize;
        while i < n
            invariant
                1 <= n <= 100000,
                n == nums.len(),
                1 <= i <= n,
                add_result as int == Self::add_state(nums@, i as int),
                sub_result as int == Self::sub_state(nums@, i as int),
            decreases n - i,
        {
            assert(i < n);
            let best_prev = if add_result >= sub_result { add_result } else { sub_result };
            let x = nums[i] as i128;
            let temp_add = best_prev.checked_add(x).unwrap_or(best_prev);
            let temp_sub = add_result.checked_sub(x).unwrap_or(add_result);
            assert(temp_add as int == Self::checked_add_or(best_prev as int, x as int, best_prev as int));
            assert(temp_sub as int == Self::checked_sub_or(add_result as int, x as int, add_result as int));
            assert(Self::add_state(nums@, i as int + 1) == Self::checked_add_or(Self::max2(Self::add_state(nums@, i as int), Self::sub_state(nums@, i as int)), nums@[i as int] as int, Self::max2(Self::add_state(nums@, i as int), Self::sub_state(nums@, i as int))));
            assert(Self::sub_state(nums@, i as int + 1) == Self::checked_sub_or(Self::add_state(nums@, i as int), nums@[i as int] as int, Self::add_state(nums@, i as int)));
            add_result = temp_add;
            sub_result = temp_sub;
            i += 1;
        }
        let best = if add_result >= sub_result { add_result } else { sub_result };
        assert(best as int == Self::max2(Self::add_state(nums@, n as int), Self::sub_state(nums@, n as int)));
        best as i64
    }
}

}
