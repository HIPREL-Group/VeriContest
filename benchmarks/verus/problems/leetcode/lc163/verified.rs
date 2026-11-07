use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_ranges(nums: Seq<i32>, i: int, next: i32, upper: i32) -> Seq<(i32, i32)>
        decreases nums.len() - i
    {
        if i >= nums.len() {
            if next <= upper {
                seq![(next, upper)]
            } else {
                seq![]
            }
        } else {
            let cur = nums[i];
            let next_after: i32 = if cur == i32::MAX { i32::MAX } else { (cur + 1) as i32 };
            if next < cur {
                seq![(next, (cur - 1) as i32)] + Self::suffix_ranges(nums, i + 1, next_after, upper)
            } else {
                Self::suffix_ranges(nums, i + 1, next_after, upper)
            }
        }
    }

    pub open spec fn result_pairs(ranges: Seq<Vec<i32>>) -> Seq<(i32, i32)> {
        Seq::new(
            ranges.len(),
            |j: int| if ranges[j].len() == 2 { (ranges[j][0], ranges[j][1]) } else { (0, 0) },
        )
    }

    pub fn find_missing_ranges(nums: Vec<i32>, lower: i32, upper: i32) -> (result: Vec<Vec<i32>>)
        requires
            0 <= nums.len() <= 100,
            lower <= upper,
            -1000000000 <= lower <= 1000000000,
            -1000000000 <= upper <= 1000000000,
            forall |i: int| 0 <= i < nums.len() ==> lower <= #[trigger] nums[i] <= upper,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
        ensures
            forall |j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            Self::result_pairs(result@) == Self::suffix_ranges(nums@, 0, lower, upper),
    {
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut next = lower;
        let mut i: usize = 0;

        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                forall |j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
                Self::result_pairs(result@) + Self::suffix_ranges(nums@, i as int, next, upper) == Self::suffix_ranges(nums@, 0, lower, upper),
            decreases nums.len() - i,
        {
            let current = nums[i];
            let next_after = if current == i32::MAX { i32::MAX } else { current + 1 };
            if next < current {
                let ghost old_result = result@;
                result.push(vec![next, current - 1]);
                proof {
                    assert(result[result.len() as int - 1].len() == 2);
                    assert(result[result.len() as int - 1][0] == next);
                    assert(result[result.len() as int - 1][1] == current - 1);
                    assert forall |j: int| 0 <= j < result.len() implies result[j].len() == 2 by {
                        if j < old_result.len() {
                            assert(result@[j] == old_result[j]);
                        } else {
                            assert(j == old_result.len());
                        }
                    };
                    assert(Self::result_pairs(result@) == Self::result_pairs(old_result) + seq![(next, (current - 1) as i32)]) by {
                        assert(Self::result_pairs(result@).len() == Self::result_pairs(old_result).len() + 1);
                        assert forall |j: int| 0 <= j < Self::result_pairs(old_result).len()
                            implies Self::result_pairs(result@)[j] == Self::result_pairs(old_result)[j] by {
                            assert(result@[j] == old_result[j]);
                        };
                        assert(Self::result_pairs(result@)[Self::result_pairs(old_result).len() as int] == (next, (current - 1) as i32));
                    };
                    assert(Self::suffix_ranges(nums@, i as int, next, upper) == seq![(next, (current - 1) as i32)] + Self::suffix_ranges(nums@, i as int + 1, next_after, upper));
                    assert(Self::result_pairs(result@) + Self::suffix_ranges(nums@, i as int + 1, next_after, upper) == Self::suffix_ranges(nums@, 0, lower, upper));
                }
            } else {
                proof {
                    assert(Self::suffix_ranges(nums@, i as int, next, upper) == Self::suffix_ranges(nums@, i as int + 1, next_after, upper));
                }
            }
            next = next_after;
            i += 1;
        }

        if next <= upper {
            let ghost old_result = result@;
            result.push(vec![next, upper]);
            proof {
                assert(result[result.len() as int - 1].len() == 2);
                assert(result[result.len() as int - 1][0] == next);
                assert(result[result.len() as int - 1][1] == upper);
                assert forall |j: int| 0 <= j < result.len() implies result[j].len() == 2 by {
                    if j < old_result.len() {
                        assert(result@[j] == old_result[j]);
                    } else {
                        assert(j == old_result.len());
                    }
                };
                assert(Self::result_pairs(result@) == Self::result_pairs(old_result) + seq![(next, upper)]) by {
                    assert(Self::result_pairs(result@).len() == Self::result_pairs(old_result).len() + 1);
                    assert forall |j: int| 0 <= j < Self::result_pairs(old_result).len()
                        implies Self::result_pairs(result@)[j] == Self::result_pairs(old_result)[j] by {
                        assert(result@[j] == old_result[j]);
                    };
                    assert(Self::result_pairs(result@)[Self::result_pairs(old_result).len() as int] == (next, upper));
                };
                assert(Self::suffix_ranges(nums@, i as int, next, upper) == seq![(next, upper)]);
            }
        } else {
            proof {
                assert(Self::suffix_ranges(nums@, i as int, next, upper) == Seq::<(i32, i32)>::empty());
            }
        }

        result
    }
}

}
