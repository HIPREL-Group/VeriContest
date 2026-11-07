use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn good_segment(nums: Seq<i64>, l: int, r: int) -> bool {
        &&& 0 <= l < r <= nums.len()
        &&& forall|t: int| l + 2 <= t < r ==> #[trigger] nums[t] == nums[t - 1] + nums[t - 2]
    }

    pub fn longest_fibonacci_segment(nums: Vec<i64>) -> (result: usize)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            1 <= result <= nums.len(),
            exists|l: int, r: int|
                #[trigger] Self::good_segment(nums@, l, r) && result as int == r - l,
            forall|l: int, r: int|
                #[trigger] Self::good_segment(nums@, l, r) ==> r - l <= result as int,
    {
        let n = nums.len();
        if n <= 2 {
            proof {
                assert(Self::good_segment(nums@, 0, n as int)) by {
                    assert forall|t: int| 0 + 2 <= t < n as int implies #[trigger] nums@[t] == nums@[t - 1] + nums@[t - 2] by {
                    };
                };
                assert(exists|l: int, r: int| Self::good_segment(nums@, l, r) && n as int == r - l) by {
                    let l = 0;
                    let r = n as int;
                    assert(Self::good_segment(nums@, l, r));
                };
                assert forall|l: int, r: int| Self::good_segment(nums@, l, r) implies r - l <= n as int by {
                    assert(r <= n as int);
                    assert(l >= 0);
                };
            }
            return n;
        }

        let mut best = 2usize;
        let ghost mut best_l: int = 0;
        let mut cur = 2usize;
        let mut i = 2usize;
        while i < n
            invariant
                n == nums.len(),
                3 <= n <= 100_000,
                2 <= i <= n,
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] nums@[j] <= 1_000_000_000,
                2 <= cur <= i,
                Self::good_segment(nums@, i as int - cur as int, i as int),
                forall|l: int|
                    0 <= l < i as int && #[trigger] Self::good_segment(nums@, l, i as int) ==> i as int - l <= cur as int,
                2 <= best <= i,
                0 <= best_l && best_l + best as int <= i as int,
                Self::good_segment(nums@, best_l, best_l + best as int),
                forall|l: int, r: int|
                    0 <= l < r <= i as int && #[trigger] Self::good_segment(nums@, l, r) ==> r - l <= best as int,
            decreases n - i,
        {
            let ghost old_best = best as int;
            let ghost old_best_l = best_l;
            let ghost old_cur = cur as int;
            let ghost old_i = i as int;
            if nums[i] == nums[i - 1] + nums[i - 2] {
                proof {
                    assert(Self::good_segment(nums@, old_i - old_cur, old_i + 1)) by {
                        assert(0 <= old_i - old_cur < old_i + 1 <= nums@.len());
                        assert forall|t: int| old_i - old_cur + 2 <= t < old_i + 1 implies #[trigger] nums@[t] == nums@[t - 1] + nums@[t - 2] by {
                            if t < old_i {
                                assert(Self::good_segment(nums@, old_i - old_cur, old_i));
                            } else {
                                assert(t == old_i);
                            }
                        };
                    };
                    assert forall|l: int|
                        0 <= l < old_i + 1 && #[trigger] Self::good_segment(nums@, l, old_i + 1) implies old_i + 1 - l <= old_cur + 1 by {
                        if l <= old_i - 2 {
                            assert(Self::good_segment(nums@, l, old_i)) by {
                                assert(0 <= l < old_i <= nums@.len());
                                assert forall|t: int| l + 2 <= t < old_i implies #[trigger] nums@[t] == nums@[t - 1] + nums@[t - 2] by {
                                    assert(Self::good_segment(nums@, l, old_i + 1));
                                };
                            };
                            assert(old_i - l <= old_cur);
                        } else if l == old_i - 1 {
                            assert(old_i + 1 - l == 2);
                            assert(2 <= old_cur + 1);
                        } else {
                            assert(l == old_i);
                            assert(old_i + 1 - l == 1);
                        }
                    };
                }
                cur = cur + 1;
            } else {
                proof {
                    assert(Self::good_segment(nums@, old_i - 1, old_i + 1)) by {
                        assert(0 <= old_i - 1 < old_i + 1 <= nums@.len());
                        assert forall|t: int| old_i - 1 + 2 <= t < old_i + 1 implies #[trigger] nums@[t] == nums@[t - 1] + nums@[t - 2] by {
                            assert(false);
                        };
                    };
                    assert forall|l: int|
                        0 <= l < old_i + 1 && #[trigger] Self::good_segment(nums@, l, old_i + 1) implies old_i + 1 - l <= 2 by {
                        if l <= old_i - 2 {
                            assert(old_i == l + 2 || old_i > l + 2);
                            assert(nums@[old_i] == nums@[old_i - 1] + nums@[old_i - 2]);
                            assert(false);
                        } else if l == old_i - 1 {
                            assert(old_i + 1 - l == 2);
                        } else {
                            assert(l == old_i);
                            assert(old_i + 1 - l == 1);
                        }
                    };
                }
                cur = 2;
            }

            let ghost cur_start = old_i + 1 - cur as int;
            if cur > best {
                proof {
                    best_l = cur_start;
                }
                best = cur;
            }
            i = i + 1;
            proof {
                assert(Self::good_segment(nums@, i as int - cur as int, i as int));
                if cur > old_best {
                    assert(best == cur);
                    assert(best_l == cur_start);
                    assert(Self::good_segment(nums@, best_l, best_l + best as int));
                    assert(best_l + best as int == i as int);
                } else {
                    assert(best == old_best);
                    assert(best_l == old_best_l);
                    assert(Self::good_segment(nums@, best_l, best_l + best as int));
                }
                assert forall|l: int, r: int|
                    0 <= l < r <= i as int && #[trigger] Self::good_segment(nums@, l, r) implies r - l <= best as int by {
                    if r < i as int {
                        assert(r <= old_i);
                        assert(r - l <= old_best);
                    } else {
                        assert(r == i as int);
                        if nums@[old_i] == nums@[old_i - 1] + nums@[old_i - 2] {
                            assert(i as int - l <= old_cur + 1);
                        } else {
                            assert(i as int - l <= 2);
                        }
                        if cur > old_best {
                            assert(best as int == cur as int);
                        } else {
                            assert(cur as int <= old_best);
                            assert(best as int == old_best);
                        }
                    }
                };
            }
        }

        proof {
            assert(exists|l: int, r: int| Self::good_segment(nums@, l, r) && best as int == r - l) by {
                let l = best_l;
                let r = best_l + best as int;
                assert(Self::good_segment(nums@, l, r));
            };
        }
        best
    }
}

}
