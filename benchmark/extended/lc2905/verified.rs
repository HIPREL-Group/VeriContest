use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(x: int, y: int) -> int {
        if x >= y {
            x - y
        } else {
            y - x
        }
    }

    pub open spec fn valid_pair(nums: Seq<i32>, index_difference: int, value_difference: int, i: int, j: int) -> bool {
        &&& 0 <= i < nums.len()
        &&& 0 <= j < nums.len()
        &&& Self::abs_diff(i, j) >= index_difference
        &&& Self::abs_diff(nums[i] as int, nums[j] as int) >= value_difference
    }

    pub proof fn lemma_abs_diff_symmetric(x: int, y: int)
        ensures
            Self::abs_diff(x, y) == Self::abs_diff(y, x),
    {
        if x >= y {
            assert(Self::abs_diff(x, y) == x - y);
            assert(Self::abs_diff(y, x) == x - y);
        } else {
            assert(Self::abs_diff(x, y) == y - x);
            assert(Self::abs_diff(y, x) == y - x);
        }
    }

    pub proof fn lemma_valid_pair_symmetric(nums: Seq<i32>, index_difference: int, value_difference: int, i: int, j: int)
        ensures
            Self::valid_pair(nums, index_difference, value_difference, i, j)
                == Self::valid_pair(nums, index_difference, value_difference, j, i),
    {
        Self::lemma_abs_diff_symmetric(i, j);
        if 0 <= i < nums.len() && 0 <= j < nums.len() {
            Self::lemma_abs_diff_symmetric(nums[i] as int, nums[j] as int);
        }
    }

    pub fn find_indices(nums: Vec<i32>, index_difference: i32, value_difference: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100_000,
            0 <= index_difference <= 100_000,
            0 <= value_difference <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result.len() == 2,
            (result[0] == -1i32) == (result[1] == -1i32),
            result[0] == -1i32 ==> forall |i: int, j: int|
                0 <= i < nums.len() && 0 <= j < nums.len()
                    ==> !Self::valid_pair(nums@, index_difference as int, value_difference as int, i, j),
            (exists |i: int, j: int| Self::valid_pair(nums@, index_difference as int, value_difference as int, i, j))
                ==> result[0] != -1i32,
            result[0] != -1i32 ==> Self::valid_pair(
                nums@,
                index_difference as int,
                value_difference as int,
                result[0] as int,
                result[1] as int,
            ),
    {
        let n = nums.len();
        let index_difference_usize = index_difference as usize;

        if index_difference_usize >= n {
            proof {
                assert forall |i: int, j: int|
                    0 <= i < nums.len() && 0 <= j < nums.len()
                        implies !Self::valid_pair(nums@, index_difference as int, value_difference as int, i, j) by {
                    if i >= j {
                        assert(Self::abs_diff(i, j) == i - j);
                        assert(i - j <= i);
                        assert(i < nums.len());
                        assert(nums.len() <= index_difference as int);
                        assert(Self::abs_diff(i, j) < index_difference as int);
                    } else {
                        assert(Self::abs_diff(i, j) == j - i);
                        assert(j - i <= j);
                        assert(j < nums.len());
                        assert(nums.len() <= index_difference as int);
                        assert(Self::abs_diff(i, j) < index_difference as int);
                    }
                }
            }
            let mut result = Vec::new();
            result.push(-1i32);
            result.push(-1i32);
            return result;
        }

        let mut r: usize = index_difference_usize;
        let mut min_idx: usize = 0;
        let mut max_idx: usize = 0;

        while r < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                0 <= index_difference <= 100_000,
                0 <= value_difference <= 1_000_000_000,
                index_difference_usize as int == index_difference as int,
                index_difference_usize < n,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
                index_difference_usize <= r <= n,
                r < n ==> 0 <= min_idx <= r - index_difference_usize,
                r < n ==> 0 <= max_idx <= r - index_difference_usize,
                r < n ==> forall |k: int|
                    0 <= k <= r as int - index_difference as int
                        ==> nums[min_idx as int] <= #[trigger] nums[k],
                r < n ==> forall |k: int|
                    0 <= k <= r as int - index_difference as int
                        ==> #[trigger] nums[k] <= nums[max_idx as int],
                forall |ii: int, jj: int|
                    index_difference as int <= jj < r as int && 0 <= ii <= jj - index_difference as int
                        ==> !Self::valid_pair(nums@, index_difference as int, value_difference as int, ii, jj),
            decreases n - r,
        {
            let high_gap = nums[max_idx] - nums[r];
            if high_gap >= value_difference {
                proof {
                    assert(max_idx as int <= r as int - index_difference as int);
                    assert(Self::abs_diff(max_idx as int, r as int) == r as int - max_idx as int) by {
                        assert(r as int >= max_idx as int);
                    }
                    assert(r as int - max_idx as int >= index_difference as int);
                    assert(nums[max_idx as int] >= nums[r as int]);
                    assert(Self::abs_diff(nums[max_idx as int] as int, nums[r as int] as int)
                        == nums[max_idx as int] as int - nums[r as int] as int);
                    assert(high_gap as int == nums[max_idx as int] as int - nums[r as int] as int);
                    assert(high_gap as int >= value_difference as int);
                    assert(Self::valid_pair(nums@, index_difference as int, value_difference as int, max_idx as int, r as int));
                }
                let mut result = Vec::new();
                result.push(max_idx as i32);
                result.push(r as i32);
                return result;
            }

            let low_gap = nums[r] - nums[min_idx];
            if low_gap >= value_difference {
                proof {
                    assert(min_idx as int <= r as int - index_difference as int);
                    assert(Self::abs_diff(min_idx as int, r as int) == r as int - min_idx as int) by {
                        assert(r as int >= min_idx as int);
                    }
                    assert(r as int - min_idx as int >= index_difference as int);
                    assert(nums[r as int] >= nums[min_idx as int]);
                    assert(Self::abs_diff(nums[min_idx as int] as int, nums[r as int] as int)
                        == nums[r as int] as int - nums[min_idx as int] as int);
                    assert(low_gap as int == nums[r as int] as int - nums[min_idx as int] as int);
                    assert(low_gap as int >= value_difference as int);
                    assert(Self::valid_pair(nums@, index_difference as int, value_difference as int, min_idx as int, r as int));
                }
                let mut result = Vec::new();
                result.push(min_idx as i32);
                result.push(r as i32);
                return result;
            }

            proof {
                assert(high_gap < value_difference);
                assert(low_gap < value_difference);
                assert forall |ii: int|
                    0 <= ii <= r as int - index_difference as int
                        implies !Self::valid_pair(nums@, index_difference as int, value_difference as int, ii, r as int) by {
                    assert(ii <= r as int);
                    assert(Self::abs_diff(ii, r as int) == r as int - ii) by {
                        assert(r as int >= ii);
                    }
                    assert(r as int - ii >= index_difference as int);
                    if nums[ii] >= nums[r as int] {
                        assert(nums[ii] <= nums[max_idx as int]);
                        assert(nums[ii] as int - nums[r as int] as int <= nums[max_idx as int] as int - nums[r as int] as int);
                        assert(Self::abs_diff(nums[ii] as int, nums[r as int] as int)
                            == nums[ii] as int - nums[r as int] as int);
                        assert(high_gap as int == nums[max_idx as int] as int - nums[r as int] as int);
                        assert(Self::abs_diff(nums[ii] as int, nums[r as int] as int) < value_difference as int);
                    } else {
                        assert(nums[min_idx as int] <= nums[ii]);
                        assert(nums[r as int] as int - nums[ii] as int <= nums[r as int] as int - nums[min_idx as int] as int);
                        assert(Self::abs_diff(nums[ii] as int, nums[r as int] as int)
                            == nums[r as int] as int - nums[ii] as int);
                        assert(low_gap as int == nums[r as int] as int - nums[min_idx as int] as int);
                        assert(Self::abs_diff(nums[ii] as int, nums[r as int] as int) < value_difference as int);
                    }
                }
                assert forall |ii: int, jj: int|
                    index_difference as int <= jj < (r + 1) as int && 0 <= ii <= jj - index_difference as int
                        implies !Self::valid_pair(nums@, index_difference as int, value_difference as int, ii, jj) by {
                    if jj < r as int {
                        assert(!Self::valid_pair(nums@, index_difference as int, value_difference as int, ii, jj));
                    } else {
                        assert(jj == r as int);
                        assert(!Self::valid_pair(nums@, index_difference as int, value_difference as int, ii, r as int));
                    }
                }
            }

            r = r + 1;
            if r < n {
                let add_idx = r - index_difference_usize;

                if nums[add_idx] < nums[min_idx] {
                    proof {
                        assert forall |k: int|
                            0 <= k <= r as int - index_difference as int
                                implies nums[add_idx as int] <= #[trigger] nums[k] by {
                            if k == add_idx as int {
                            } else {
                                assert(0 <= k <= r as int - index_difference as int - 1);
                                assert(nums[min_idx as int] <= nums[k]);
                                assert(nums[add_idx as int] < nums[min_idx as int]);
                            }
                        }
                    }
                    min_idx = add_idx;
                } else {
                    proof {
                        assert forall |k: int|
                            0 <= k <= r as int - index_difference as int
                                implies nums[min_idx as int] <= #[trigger] nums[k] by {
                            if k == add_idx as int {
                                assert(nums[min_idx as int] <= nums[add_idx as int]);
                            } else {
                                assert(0 <= k <= r as int - index_difference as int - 1);
                                assert(nums[min_idx as int] <= nums[k]);
                            }
                        }
                    }
                }

                if nums[add_idx] > nums[max_idx] {
                    proof {
                        assert forall |k: int|
                            0 <= k <= r as int - index_difference as int
                                implies #[trigger] nums[k] <= nums[add_idx as int] by {
                            if k == add_idx as int {
                            } else {
                                assert(0 <= k <= r as int - index_difference as int - 1);
                                assert(nums[k] <= nums[max_idx as int]);
                                assert(nums[max_idx as int] < nums[add_idx as int]);
                            }
                        }
                    }
                    max_idx = add_idx;
                } 
            }
        }

        proof {
            assert forall |i: int, j: int|
                0 <= i < nums.len() && 0 <= j < nums.len()
                    implies !Self::valid_pair(nums@, index_difference as int, value_difference as int, i, j) by {
                if i <= j {
                    assert(Self::abs_diff(i, j) == j - i);
                    if Self::abs_diff(i, j) >= index_difference as int {
                        assert(index_difference as int <= j);
                        assert(i <= j - index_difference as int);
                        assert(!Self::valid_pair(nums@, index_difference as int, value_difference as int, i, j));
                    }
                } else {
                    assert(Self::abs_diff(i, j) == i - j);
                    if Self::abs_diff(i, j) >= index_difference as int {
                        assert(index_difference as int <= i);
                        assert(j <= i - index_difference as int);
                        assert(!Self::valid_pair(nums@, index_difference as int, value_difference as int, j, i));
                        Self::lemma_valid_pair_symmetric(nums@, index_difference as int, value_difference as int, i, j);
                    }
                }
            }
        }
        let mut result = Vec::new();
        result.push(-1i32);
        result.push(-1i32);
        result
    }
}

}
