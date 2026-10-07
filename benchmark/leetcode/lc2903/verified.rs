use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_int(x: int) -> int {
        if x < 0 { -x } else { x }
    }

    pub open spec fn valid_pair(nums: Seq<i32>, i: int, j: int, index_difference: int, value_difference: int) -> bool
        recommends
            0 <= i < nums.len(),
            0 <= j < nums.len(),
            0 <= index_difference,
            0 <= value_difference,
    {
        Self::abs_int(i - j) >= index_difference
            && Self::abs_int(nums[i] as int - nums[j] as int) >= value_difference
    }

    pub fn find_indices(nums: Vec<i32>, index_difference: i32, value_difference: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            0 <= index_difference <= 100,
            0 <= value_difference <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50,
        ensures
            result.len() == 2,
            result[0] == -1 ==> result[1] == -1,
            result[0] != -1 ==> (
                0 <= result[0] < nums.len() as i32
                && 0 <= result[1] < nums.len() as i32
                && Self::valid_pair(nums@, result[0] as int, result[1] as int, index_difference as int, value_difference as int)
            ),
            result[0] == -1 ==> (
                forall |i: i32, j: i32|
                    0 <= i < nums.len() as i32 && 0 <= j < nums.len() as i32
                    ==> !Self::valid_pair(nums@, i as int, j as int, index_difference as int, value_difference as int)
            ),
    {
        let mut i: i32 = 0;
        while i < nums.len() as i32
            invariant
                0 <= i <= nums.len() as i32,
                forall |a: i32, b: i32|
                    0 <= a < i && 0 <= b < nums.len() as i32
                    ==> !Self::valid_pair(nums@, a as int, b as int, index_difference as int, value_difference as int),
            decreases nums.len() as i32 - i,
        {
            let mut j: i32 = 0;
            while j < nums.len() as i32
                invariant
                    0 <= j <= nums.len() as i32,
                    0 <= i < nums.len() as i32,
                    forall |a: i32, b: i32|
                        0 <= a < i && 0 <= b < nums.len() as i32
                        ==> !Self::valid_pair(nums@, a as int, b as int, index_difference as int, value_difference as int),
                    forall |b: i32|
                        0 <= b < j
                        ==> !Self::valid_pair(nums@, i as int, b as int, index_difference as int, value_difference as int),
                decreases nums.len() as i32 - j,
            {
                let idx_gap: i32 = if i >= j { i - j } else { j - i };
                let val_gap: i64 = if nums[i as usize] >= nums[j as usize] {
                    nums[i as usize] as i64 - nums[j as usize] as i64
                } else {
                    nums[j as usize] as i64 - nums[i as usize] as i64
                };
                if idx_gap >= index_difference && val_gap >= value_difference as i64 {
                    assert(0 <= i as int);
                    assert((i as int) < nums.len());
                    assert(0 <= j as int);
                    assert((j as int) < nums.len());
                    assert(Self::abs_int((i as int) - (j as int)) == idx_gap as int) by {
                        if i >= j {
                            assert(idx_gap == i - j);
                            assert(Self::abs_int((i as int) - (j as int)) == (i as int) - (j as int));
                        } else {
                            assert(idx_gap == j - i);
                            assert((i as int) - (j as int) < 0);
                            assert(Self::abs_int((i as int) - (j as int)) == (j as int) - (i as int));
                        }
                    };
                    assert(Self::abs_int((nums@[i as int] as int) - (nums@[j as int] as int)) == val_gap as int) by {
                        if nums[i as int] >= nums[j as int] {
                            assert(val_gap == nums[i as int] as i64 - nums[j as int] as i64);
                            assert(Self::abs_int((nums@[i as int] as int) - (nums@[j as int] as int)) == (nums@[i as int] as int) - (nums@[j as int] as int));
                        } else {
                            assert(val_gap == nums[j as int] as i64 - nums[i as int] as i64);
                            assert((nums@[i as int] as int) - (nums@[j as int] as int) < 0);
                            assert(Self::abs_int((nums@[i as int] as int) - (nums@[j as int] as int)) == (nums@[j as int] as int) - (nums@[i as int] as int));
                        }
                    };
                    return vec![i, j];
                }
                assert(!(idx_gap >= index_difference && val_gap >= value_difference as i64));
                assert(Self::abs_int((i as int) - (j as int)) == idx_gap as int) by {
                    if i >= j {
                        assert(idx_gap == i - j);
                        assert(Self::abs_int((i as int) - (j as int)) == (i as int) - (j as int));
                    } else {
                        assert(idx_gap == j - i);
                        assert((i as int) - (j as int) < 0);
                        assert(Self::abs_int((i as int) - (j as int)) == (j as int) - (i as int));
                    }
                };
                assert(Self::abs_int((nums@[i as int] as int) - (nums@[j as int] as int)) == val_gap as int) by {
                    if nums[i as int] >= nums[j as int] {
                        assert(val_gap == nums[i as int] as i64 - nums[j as int] as i64);
                        assert(Self::abs_int((nums@[i as int] as int) - (nums@[j as int] as int)) == (nums@[i as int] as int) - (nums@[j as int] as int));
                    } else {
                        assert(val_gap == nums[j as int] as i64 - nums[i as int] as i64);
                        assert((nums@[i as int] as int) - (nums@[j as int] as int) < 0);
                        assert(Self::abs_int((nums@[i as int] as int) - (nums@[j as int] as int)) == (nums@[j as int] as int) - (nums@[i as int] as int));
                    }
                };
                assert(!Self::valid_pair(nums@, i as int, j as int, index_difference as int, value_difference as int));
                assert forall |b: i32|
                    0 <= b < j + 1
                    implies !Self::valid_pair(nums@, i as int, b as int, index_difference as int, value_difference as int)
                by {
                    if b < j {
                        assert(!Self::valid_pair(nums@, i as int, b as int, index_difference as int, value_difference as int));
                    } else {
                        assert(b == j);
                        assert(!Self::valid_pair(nums@, i as int, j as int, index_difference as int, value_difference as int));
                    }
                };
                j = j + 1;
            }
            assert(j == nums.len() as i32);
            assert forall |a: i32, b: i32|
                0 <= a < i + 1 && 0 <= b < nums.len() as i32
                implies !Self::valid_pair(nums@, a as int, b as int, index_difference as int, value_difference as int)
            by {
                if a < i {
                    assert(!Self::valid_pair(nums@, a as int, b as int, index_difference as int, value_difference as int));
                } else {
                    assert(a == i);
                    assert(b < j);
                    assert(!Self::valid_pair(nums@, i as int, b as int, index_difference as int, value_difference as int));
                }
            };
            i = i + 1;
        }
        assert(i == nums.len() as i32);
        assert(forall |a: i32, b: i32|
            0 <= a < nums.len() as i32 && 0 <= b < nums.len() as i32
            ==> !Self::valid_pair(nums@, a as int, b as int, index_difference as int, value_difference as int));
        vec![-1, -1]
    }
}

}
