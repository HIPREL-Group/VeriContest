use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value(nums: Seq<i32>, end: int, value: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_value(nums, end - 1, value)
                + if nums[end - 1] as int == value { 1int } else { 0int }
        }
    }

    pub open spec fn xor_twice_upto(nums: Seq<i32>, upto: int) -> i32
        decreases upto,
    {
        if upto <= 0 {
            0i32
        } else {
            Self::xor_twice_upto(nums, upto - 1)
                ^ if Self::count_value(nums, nums.len() as int, upto) == 2 { upto as i32 } else { 0i32 }
        }
    }

    pub open spec fn duplicate_numbers_xor_spec(nums: Seq<i32>) -> i32 {
        Self::xor_twice_upto(nums, 50)
    }

    proof fn lemma_count_value_mono(nums: Seq<i32>, value: int, e1: int, e2: int)
        requires
            0 <= e1 <= e2 <= nums.len(),
        ensures
            Self::count_value(nums, e1, value) <= Self::count_value(nums, e2, value),
        decreases e2 - e1,
    {
        if e1 == e2 {
        } else {
            Self::lemma_count_value_mono(nums, value, e1, e2 - 1);
            assert(Self::count_value(nums, e2, value)
                == Self::count_value(nums, e2 - 1, value)
                    + if nums[e2 - 1] as int == value { 1int } else { 0int });
            assert(Self::count_value(nums, e2 - 1, value) <= Self::count_value(nums, e2, value));
        }
    }

    pub fn duplicate_numbers_xor(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
            forall |v: int| 1 <= v <= 50 ==> 0 <= #[trigger] Self::count_value(nums@, nums.len() as int, v) <= 2,
        ensures
            result == Self::duplicate_numbers_xor_spec(nums@),
    {
        let mut freq: Vec<i32> = vec![0i32; 51];
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                1 <= nums.len() <= 50,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 50,
                forall |v: int| 1 <= v <= 50 ==> 0 <= #[trigger] Self::count_value(nums@, nums.len() as int, v) <= 2,
                freq.len() == 51,
                0 <= i <= nums.len(),
                forall |v: int| 1 <= v <= 50 ==> #[trigger] freq[v] == Self::count_value(nums@, i as int, v),
            decreases nums.len() - i,
        {
            let idx: usize = nums[i] as usize;
            proof {
                let vidx = idx as int;
                assert(1 <= vidx <= 50);
                assert(freq[vidx] == Self::count_value(nums@, i as int, vidx));
                assert(Self::count_value(nums@, i as int + 1, vidx)
                    == Self::count_value(nums@, i as int, vidx) + 1);
                Self::lemma_count_value_mono(nums@, vidx, i as int + 1, nums.len() as int);
                assert(Self::count_value(nums@, i as int + 1, vidx)
                    <= Self::count_value(nums@, nums.len() as int, vidx));
                assert(Self::count_value(nums@, nums.len() as int, vidx) <= 2);
                assert(freq[vidx] <= 1);
            }
            if freq[idx] <= 1 {
                freq.set(idx, freq[idx] + 1);
            }
            i = i + 1;
        }

        let mut ans: i32 = 0;
        let mut v: usize = 1;
        while v <= 50
            invariant
                1 <= nums.len() <= 50,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 50,
                forall |x: int| 1 <= x <= 50 ==> 0 <= #[trigger] Self::count_value(nums@, nums.len() as int, x) <= 2,
                freq.len() == 51,
                forall |x: int| 1 <= x <= 50 ==> #[trigger] freq[x] == Self::count_value(nums@, nums.len() as int, x),
                1 <= v <= 51,
                ans == Self::xor_twice_upto(nums@, v as int - 1),
            decreases 51 - v,
        {
            let ghost old_ans = ans;
            if freq[v] == 2 {
                ans = ans ^ v as i32;
            }
            proof {
                assert(Self::xor_twice_upto(nums@, v as int)
                    == Self::xor_twice_upto(nums@, v as int - 1)
                        ^ if Self::count_value(nums@, nums.len() as int, v as int) == 2 { v as i32 } else { 0i32 });
                assert(old_ans == Self::xor_twice_upto(nums@, v as int - 1));
                if freq[v as int] == 2 {
                    assert(Self::count_value(nums@, nums.len() as int, v as int) == 2);
                    assert(ans == old_ans ^ v as i32);
                    assert(ans == Self::xor_twice_upto(nums@, v as int));
                } else {
                    assert(Self::count_value(nums@, nums.len() as int, v as int) != 2);
                    assert(ans == old_ans);
                    assert(Self::xor_twice_upto(nums@, v as int)
                        == Self::xor_twice_upto(nums@, v as int - 1) ^ 0i32);
                    assert(old_ans ^ 0i32 == old_ans) by(bit_vector);
                    assert(ans == Self::xor_twice_upto(nums@, v as int));
                }
            }
            v = v + 1;
        }
        ans
    }
}

}
