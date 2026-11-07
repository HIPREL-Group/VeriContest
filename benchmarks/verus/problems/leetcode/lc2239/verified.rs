use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_closest_number(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            exists|idx: int| 0 <= idx < nums.len() && nums[idx] == res,
            forall|i: int|
                0 <= i < nums.len() ==> (if res >= 0 { res as int } else { -(res as int) })
                    <= (if #[trigger] nums[i] >= 0 { nums[i] as int } else { -(nums[i] as int) }),
            forall|i: int|
                0 <= i < nums.len() &&
                (if res >= 0 { res as int } else { -(res as int) })
                    == (if #[trigger] nums[i] >= 0 { nums[i] as int } else { -(nums[i] as int) })
                    ==> nums[i] <= res,
    {
        let n = nums.len();
        let mut best = nums[0];
        let mut i: usize = 1;

        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 1000,
                1 <= i <= n,
                forall|k: int| 0 <= k < nums.len() ==> -100_000 <= #[trigger] nums[k] <= 100_000,
                -100_000 <= best <= 100_000,
                exists|idx: int| 0 <= idx < i && nums[idx] == best,
                forall|k: int|
                    0 <= k < i ==> (if best >= 0 { best as int } else { -(best as int) })
                        <= (if #[trigger] nums[k] >= 0 { nums[k] as int } else { -(nums[k] as int) }),
                forall|k: int|
                    0 <= k < i &&
                    (if best >= 0 { best as int } else { -(best as int) })
                        == (if #[trigger] nums[k] >= 0 { nums[k] as int } else { -(nums[k] as int) })
                        ==> nums[k] <= best,
            decreases n - i,
        {
            let current = nums[i];
            let prev_best = best;
            let prev_best_abs = if prev_best < 0 { -prev_best } else { prev_best };
            let current_abs = if current < 0 { -current } else { current };
            let new_best = if current_abs < prev_best_abs || (current_abs == prev_best_abs && current > prev_best) {
                current
            } else {
                prev_best
            };

            proof {
                assert(-100_000 <= current <= 100_000);
                assert(0 <= current_abs <= 100_000);
                assert(0 <= prev_best_abs <= 100_000);
                assert(-100_000 <= new_best <= 100_000);

                assert(exists|idx: int| 0 <= idx < i + 1 && nums[idx] == new_best) by {
                    if new_best == current {
                        assert(nums[i as int] == new_best);
                    } else {
                        let idx = choose|idx: int| 0 <= idx < i && nums[idx] == prev_best;
                        assert(0 <= idx < i + 1);
                        assert(nums[idx] == new_best);
                    }
                }

                assert forall|k: int|
                    0 <= k < i + 1 implies (if new_best >= 0 { new_best as int } else { -(new_best as int) })
                        <= (if #[trigger] nums[k] >= 0 { nums[k] as int } else { -(nums[k] as int) }) by {
                    if k < i {
                        assert(prev_best_abs <= (if nums[k] >= 0 { nums[k] as int } else { -(nums[k] as int) }));
                        if new_best == current {
                            if current_abs < prev_best_abs {
                                assert((if new_best >= 0 { new_best as int } else { -(new_best as int) }) == current_abs as int);
                                assert(current_abs < prev_best_abs);
                            } else {
                                assert(current_abs == prev_best_abs);
                                assert((if new_best >= 0 { new_best as int } else { -(new_best as int) }) == current_abs as int);
                            }
                        } else {
                            assert(new_best == prev_best);
                        }
                    } else {
                        assert(k == i as int);
                        if new_best == current {
                            assert((if new_best >= 0 { new_best as int } else { -(new_best as int) })
                                == (if nums[k] >= 0 { nums[k] as int } else { -(nums[k] as int) }));
                        } else {
                            assert(new_best == prev_best);
                            assert(prev_best_abs <= current_abs);
                            assert((if nums[k] >= 0 { nums[k] as int } else { -(nums[k] as int) }) == current_abs as int);
                        }
                    }
                }

                assert forall|k: int|
                    0 <= k < i + 1 &&
                    (if new_best >= 0 { new_best as int } else { -(new_best as int) })
                        == (if #[trigger] nums[k] >= 0 { nums[k] as int } else { -(nums[k] as int) })
                        implies nums[k] <= new_best by {
                    if k < i {
                        if new_best == current {
                            if current_abs < prev_best_abs {
                                assert(false);
                            } else {
                                assert(current_abs == prev_best_abs);
                                assert(nums[k] <= prev_best);
                                assert(prev_best <= current) by {
                                    if current < prev_best {
                                        assert(!(current_abs < prev_best_abs || (current_abs == prev_best_abs && current > prev_best)));
                                        assert(new_best == prev_best);
                                        assert(new_best == current);
                                    }
                                }
                                assert(new_best == current);
                            }
                        } else {
                            assert(new_best == prev_best);
                            assert(nums[k] <= prev_best);
                        }
                    } else {
                        assert(k == i as int);
                        assert(nums[k] == current);
                        if new_best == current {
                            assert(nums[k] <= new_best);
                        } else {
                            assert(new_best == prev_best);
                            assert(prev_best_abs <= current_abs);
                            if prev_best_abs == current_abs {
                                assert(!(current > prev_best));
                                assert(current <= prev_best);
                                assert(nums[k] <= new_best);
                            }
                        }
                    }
                }
            }

            best = new_best;
            i += 1;
        }

        best
    }
}

}
