use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_global_max(nums: Seq<i32>, value: i32) -> bool
    {
        &&& exists|idx: int| 0 <= idx < nums.len() && nums[idx] == value
        &&& forall|idx: int| 0 <= idx < nums.len() ==> #[trigger] nums[idx] <= value
    }

    pub open spec fn is_constant_block(nums: Seq<i32>, value: i32, start: int, len: int) -> bool
    {
        &&& 0 <= start
        &&& 0 <= len
        &&& start + len <= nums.len()
        &&& forall|idx: int| start <= idx < start + len ==> #[trigger] nums[idx] == value
    }

    pub open spec fn is_constant_until(nums: Seq<i32>, value: i32, start: int, end: int) -> bool
    {
        &&& 0 <= start <= end <= nums.len()
        &&& forall|idx: int| start <= idx < end ==> #[trigger] nums[idx] == value
    }

    pub fn longest_subarray(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 1_000_000,
        ensures
            1 <= res,
            res as int <= nums.len() as int,
            exists|value: i32| {
                &&& Self::is_global_max(nums@, value)
                &&& exists|start: int| Self::is_constant_block(nums@, value, start, res as int)
                &&& forall|start: int, len: int|
                        Self::is_constant_block(nums@, value, start, len) && 1 <= len
                        ==> len <= res as int
            },
    {
        let mut max_val = nums[0];
        let mut i = 1usize;
        while i < nums.len()
            invariant
                1 <= nums.len() <= 100_000,
                forall|idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 1_000_000,
                1 <= i <= nums.len(),
                1 <= max_val <= 1_000_000,
                exists|idx: int| 0 <= idx < i as int && nums[idx] == max_val,
                forall|idx: int| 0 <= idx < i as int ==> #[trigger] nums[idx] <= max_val,
            decreases nums.len() - i,
        {
            let x = nums[i];
            if x > max_val {
                max_val = x;
            }
            i = i + 1;
        }

        proof {
            assert(Self::is_global_max(nums@, max_val));
        }

        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut j: usize = 0;
        let ghost mut best_start: int = 0;
        while j < nums.len()
            invariant
                1 <= nums.len() <= 100_000,
                forall|idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 1_000_000,
                1 <= max_val <= 1_000_000,
                Self::is_global_max(nums@, max_val),
                0 <= j <= nums.len(),
                0 <= cur <= 100_000,
                0 <= best <= 100_000,
                cur as int <= j as int,
                best as int <= j as int,
                0 <= best_start <= j as int,
                0 < best ==> Self::is_constant_block(nums@, max_val, best_start, best as int),
                0 < best ==> best_start + best as int <= j as int,
                forall|idx: int| j as int - cur as int <= idx < j as int ==> #[trigger] nums[idx] == max_val,
                forall|start: int|
                    0 <= start <= j as int &&
                    #[trigger] Self::is_constant_until(nums@, max_val, start, j as int)
                    ==> j as int - start <= cur as int,
                forall|start: int, len: int|
                    0 <= start && 1 <= len && start + len <= j as int &&
                    #[trigger] Self::is_constant_block(nums@, max_val, start, len)
                    ==> len <= best as int,
            decreases nums.len() - j,
        {
            let ghost old_j: int = j as int;
            let ghost old_cur: int = cur as int;
            let ghost old_best: int = best as int;
            let ghost old_best_start: int = best_start;
            let x = nums[j];

            if x == max_val {
                proof {
                    assert(cur < i32::MAX) by (nonlinear_arith)
                        requires
                            cur as int <= j as int,
                            j < nums.len(),
                            nums.len() <= 100_000,
                    {
                    }
                }
                cur = cur + 1;
                if best < cur {
                    best = cur;
                    proof {
                        best_start = old_j + 1 - cur as int;
                    }
                }

                proof {
                    if old_best < cur as int {
                        assert(best as int == cur as int);
                    } else {
                        assert(best as int == old_best);
                    }
                    assert(old_best <= best as int);
                    assert(cur as int <= best as int);
                    assert(cur as int == old_cur + 1);
                    assert(old_j + 1 - cur as int == old_j - old_cur);

                    assert forall|idx: int|
                        old_j + 1 - cur as int <= idx < old_j + 1
                        implies #[trigger] nums@[idx] == max_val by
                    {
                        if idx < old_j {
                            assert(old_j - old_cur <= idx < old_j);
                            assert(nums@[idx] == max_val);
                        } else {
                            assert(idx == old_j);
                            assert(nums@[idx] == x);
                        }
                    };

                    assert forall|start: int|
                        0 <= start <= old_j + 1 &&
                        #[trigger] Self::is_constant_until(nums@, max_val, start, old_j + 1)
                        implies old_j + 1 - start <= cur as int by
                    {
                        if start < old_j + 1 {
                            assert forall|idx: int| start <= idx < old_j implies #[trigger] nums@[idx] == max_val by {
                                assert(start <= idx < old_j + 1);
                                assert(nums@[idx] == max_val);
                            };
                            assert(Self::is_constant_until(nums@, max_val, start, old_j));
                            assert(old_j - start <= old_cur);
                        } else {
                            assert(old_j + 1 - start == 0);
                        }
                    };

                    assert forall|start: int, len: int|
                        0 <= start && 1 <= len && start + len <= old_j + 1 &&
                        #[trigger] Self::is_constant_block(nums@, max_val, start, len)
                        implies len <= best as int by
                    {
                        if start + len <= old_j {
                            assert(len <= old_best);
                            assert(old_best <= best as int);
                        } else {
                            assert(start + len == old_j + 1);
                            assert(Self::is_constant_until(nums@, max_val, start, old_j + 1));
                            assert(old_j + 1 - start <= cur as int);
                            assert(len == old_j + 1 - start);
                            assert(len <= cur as int);
                            assert(cur as int <= best as int);
                        }
                    };

                    if 0 < best {
                        if old_best < cur as int {
                            assert(best as int == cur as int);
                            assert(best_start == old_j + 1 - cur as int);
                            assert(Self::is_constant_block(nums@, max_val, best_start, best as int)) by {
                                assert(0 <= best_start);
                                assert(best_start + best as int <= nums.len());
                                assert forall|idx: int|
                                    best_start <= idx < best_start + best as int
                                    implies #[trigger] nums@[idx] == max_val by
                                {
                                    assert(old_j + 1 - cur as int <= idx < old_j + 1);
                                    assert(nums@[idx] == max_val);
                                };
                            };
                        } else {
                            assert(best as int == old_best);
                            assert(best_start == old_best_start);
                        }
                    }
                }
            } else {
                cur = 0;
                proof {
                    assert(best as int == old_best);
                    assert(best_start == old_best_start);

                    assert forall|start: int|
                        0 <= start <= old_j + 1 &&
                        #[trigger] Self::is_constant_until(nums@, max_val, start, old_j + 1)
                        implies old_j + 1 - start <= cur as int by
                    {
                        if start < old_j + 1 {
                            assert(start <= old_j < old_j + 1);
                            assert(nums@[old_j] == max_val);
                            assert(nums@[old_j] == x);
                            assert(false);
                        } else {
                            assert(old_j + 1 - start == 0);
                        }
                    };

                    assert forall|start: int, len: int|
                        0 <= start && 1 <= len && start + len <= old_j + 1 &&
                        #[trigger] Self::is_constant_block(nums@, max_val, start, len)
                        implies len <= best as int by
                    {
                        if start + len <= old_j {
                            assert(len <= best as int);
                        } else {
                            assert(start + len == old_j + 1);
                            assert(start <= old_j < start + len);
                            assert(nums@[old_j] == max_val);
                            assert(nums@[old_j] == x);
                            assert(false);
                        }
                    };
                }
            }

            j = j + 1;
        }

        proof {
            let idx_max = choose|idx: int| 0 <= idx < nums.len() && nums@[idx] == max_val;
            assert(Self::is_constant_block(nums@, max_val, idx_max, 1)) by {
                assert(0 <= idx_max);
                assert(idx_max + 1 <= nums.len());
                assert forall|idx: int| idx_max <= idx < idx_max + 1 implies #[trigger] nums@[idx] == max_val by {
                    assert(idx == idx_max);
                };
            };
            assert(1 <= best as int);
            assert(0 < best);

            assert(exists|value: i32| {
                &&& Self::is_global_max(nums@, value)
                &&& exists|start: int| Self::is_constant_block(nums@, value, start, best as int)
                &&& forall|start: int, len: int|
                        Self::is_constant_block(nums@, value, start, len) && 1 <= len
                        ==> len <= best as int
            }) by {
                assert(Self::is_global_max(nums@, max_val));
                assert(Self::is_constant_block(nums@, max_val, best_start, best as int));
                assert(exists|start: int| Self::is_constant_block(nums@, max_val, start, best as int));
                assert forall|start: int, len: int|
                    Self::is_constant_block(nums@, max_val, start, len) && 1 <= len
                    implies len <= best as int by {
                    if Self::is_constant_block(nums@, max_val, start, len) && 1 <= len {
                        assert(start + len <= nums.len());
                        assert(len <= best as int);
                    }
                };
            };
        }

        best
    }
}

} 
