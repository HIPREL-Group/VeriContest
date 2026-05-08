use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn max_int(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn popcount_helper(x: int, acc: int) -> int
        decreases x,
    {
        if x <= 0 {
            acc
        } else {
            Self::popcount_helper(x / 2, acc + (x % 2))
        }
    }

    pub open spec fn popcount(x: int) -> int {
        Self::popcount_helper(x, 0)
    }

    proof fn lemma_popcount_helper_additive(x: int, acc: int)
        requires
            x >= 0,
            acc >= 0,
        ensures
            Self::popcount_helper(x, acc) == Self::popcount(x) + acc,
            Self::popcount_helper(x, acc) >= acc,
        decreases x,
    {
        if x > 0 {
            Self::lemma_popcount_helper_additive(x / 2, acc + (x % 2));
            Self::lemma_popcount_helper_additive(x / 2, x % 2);
            assert(x % 2 >= 0);
        }
    }

    proof fn lemma_popcount_step(x: int)
        requires
            x >= 0,
        ensures
            Self::popcount(x) == Self::popcount(x / 2) + (x % 2),
    {
        Self::lemma_popcount_helper_additive(x / 2, x % 2);
    }

    proof fn lemma_popcount_le(x: int)
        requires
            x >= 0,
        ensures
            Self::popcount(x) <= x,
        decreases x,
    {
        if x > 0 {
            Self::lemma_popcount_le(x / 2);
            Self::lemma_popcount_step(x);
            assert(0 <= x % 2 <= 1);
            assert(x / 2 + (x % 2) <= x) by (nonlinear_arith)
                requires
                    x >= 0,
            {
            }
        }
    }

    pub open spec fn scan_spec(
        nums: Seq<i32>,
        i: int,
        has_prev: bool,
        prev_max: int,
        curr_bits: int,
        curr_min: int,
        curr_max: int,
    ) -> bool
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            !has_prev || prev_max <= curr_min
        } else {
            let x = nums[i] as int;
            let b = Self::popcount(x);
            if b == curr_bits {
                Self::scan_spec(
                    nums,
                    i + 1,
                    has_prev,
                    prev_max,
                    curr_bits,
                    Self::min_int(curr_min, x),
                    Self::max_int(curr_max, x),
                )
            } else {
                (!has_prev || prev_max <= curr_min)
                && Self::scan_spec(nums, i + 1, true, curr_max, b, x, x)
            }
        }
    }

    pub open spec fn can_sort_array_spec(nums: Seq<i32>) -> bool {
        if nums.len() == 0 {
            true
        } else {
            let x0 = nums[0] as int;
            Self::scan_spec(nums, 1, false, 0, Self::popcount(x0), x0, x0)
        }
    }

    fn popcount_exec(x: i32) -> (bits: i32)
        requires
            0 <= x <= 256,
        ensures
            bits as int == Self::popcount(x as int),
    {
        let ghost x0 = x as int;
        let mut y = x as u32;
        let mut bits = 0i32;
        while y > 0
            invariant
                0 <= y as int <= x0 <= 256,
                0 <= bits,
                Self::popcount_helper(y as int, bits as int) == Self::popcount(x0),
            decreases y as int,
        {
            let ghost old_y = y as int;
            let ghost old_bits = bits as int;
            let bit = y % 2;
            proof {
                assert(0 < old_y);
                assert(0 <= old_y % 2 <= 1);
                Self::lemma_popcount_helper_additive(old_y, old_bits);
                Self::lemma_popcount_le(x0);
                assert(old_bits <= Self::popcount_helper(old_y, old_bits));
                assert(old_bits <= Self::popcount(x0));
                assert(old_bits <= x0);
                assert(old_bits + (old_y % 2) <= 257);
                assert(Self::popcount_helper(old_y, old_bits) == Self::popcount_helper(old_y / 2, old_bits + (old_y % 2)));
                assert(old_bits + (old_y % 2) >= 0);
                assert(old_bits + (bit as int) == old_bits + (old_y % 2));
                assert(0 <= (y % 2) as i32 <= 1);
                assert(bits <= 256);
                assert(bits + (y % 2) as i32 <= 257);
            }
            bits += (y % 2) as i32;
            y /= 2;
            proof {
                assert(y as int == old_y / 2);
                assert(bits as int == old_bits + (old_y % 2));
                assert(Self::popcount_helper(y as int, bits as int) == Self::popcount(x0));
            }
        }
        proof {
            assert(y == 0);
            assert(Self::popcount_helper(0, bits as int) == bits as int);
            assert(bits as int == Self::popcount(x0));
        }
        bits
    }

    pub fn can_sort_array(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 256,
        ensures
            result <==> Self::can_sort_array_spec(nums@),
    {
        let n = nums.len();
        let mut i: usize = 1;
        let mut prev_max: i32 = 0;
        let mut has_prev: bool = false;

        let mut curr_bits: i32 = Self::popcount_exec(nums[0]);
        let mut curr_min: i32 = nums[0];
        let mut curr_max: i32 = nums[0];

        let result = Self::can_sort_array_impl(&nums, n, i, prev_max, has_prev, curr_bits, curr_min, curr_max);
        result
    }

    fn can_sort_array_impl(
        nums: &Vec<i32>,
        n: usize,
        i: usize,
        prev_max: i32,
        has_prev: bool,
        curr_bits: i32,
        curr_min: i32,
        curr_max: i32,
    ) -> (result: bool)
        requires
            n == nums.len(),
            1 <= n <= 100,
            1 <= i <= n,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 256,
            0 <= prev_max <= 256,
            1 <= curr_min <= 256,
            1 <= curr_max <= 256,
            Self::scan_spec(nums@, i as int, has_prev, prev_max as int, curr_bits as int, curr_min as int, curr_max as int)
                == Self::can_sort_array_spec(nums@),
        ensures
            result <==> Self::can_sort_array_spec(nums@),
        decreases n - i,
    {
        if i >= n {
            proof {
                assert(i as int >= nums@.len());
                assert(Self::scan_spec(nums@, i as int, has_prev, prev_max as int, curr_bits as int, curr_min as int, curr_max as int)
                    == (!has_prev || prev_max as int <= curr_min as int));
                assert((!has_prev || prev_max <= curr_min) == (!has_prev || prev_max as int <= curr_min as int));
                assert((!has_prev || prev_max <= curr_min) == Self::scan_spec(nums@, i as int, has_prev, prev_max as int, curr_bits as int, curr_min as int, curr_max as int));
                assert((!has_prev || prev_max <= curr_min) == Self::can_sort_array_spec(nums@));
            }
            !has_prev || prev_max <= curr_min
        } else {
            let x = nums[i];
            let b = Self::popcount_exec(x);
            if b == curr_bits {
                let mut next_curr_min = curr_min;
                let mut next_curr_max = curr_max;
                if x < next_curr_min {
                    next_curr_min = x;
                }
                if x > next_curr_max {
                    next_curr_max = x;
                }
                proof {
                    assert(next_curr_min as int == Self::min_int(curr_min as int, x as int));
                    assert(next_curr_max as int == Self::max_int(curr_max as int, x as int));
                    assert(Self::scan_spec(nums@, i as int, has_prev, prev_max as int, curr_bits as int, curr_min as int, curr_max as int)
                        == Self::scan_spec(
                            nums@,
                            i as int + 1,
                            has_prev,
                            prev_max as int,
                            curr_bits as int,
                            next_curr_min as int,
                            next_curr_max as int,
                        ));
                }
                Self::can_sort_array_impl(nums, n, i + 1, prev_max, has_prev, curr_bits, next_curr_min, next_curr_max)
            } else {
                if has_prev && prev_max > curr_min {
                    proof {
                        assert((!has_prev || prev_max as int <= curr_min as int) == false);
                        assert(Self::scan_spec(nums@, i as int, has_prev, prev_max as int, curr_bits as int, curr_min as int, curr_max as int) == false);
                        assert(Self::can_sort_array_spec(nums@) == false);
                    }
                    false
                } else {
                    proof {
                        assert(!has_prev || prev_max <= curr_min);
                        assert(Self::scan_spec(nums@, i as int, has_prev, prev_max as int, curr_bits as int, curr_min as int, curr_max as int)
                            == Self::scan_spec(nums@, i as int + 1, true, curr_max as int, b as int, x as int, x as int));
                    }
                    Self::can_sort_array_impl(nums, n, i + 1, curr_max, true, b, x, x)
                }
            }
        }
    }
}

}
