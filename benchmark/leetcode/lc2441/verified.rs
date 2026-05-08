use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_max_k(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> nums[i] != 0,
        ensures
            res == -1 || 1 <= res <= 1000,
            (res == -1) == !(exists |p: int, q: int|
                0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] > 0 && nums[q] == -nums[p]),
            res >= 1 ==> exists |p: int, q: int|
                0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] == res && nums[q] == -res,
            res >= 1 ==> forall |p: int, q: int|
                0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] > 0 && nums[q] == -nums[p]
                    ==> nums[p] <= res,
    {
        let n = nums.len();
        let mut best = -1;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> -1000 <= #[trigger] nums[k] <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> nums[k] != 0,
                0 <= i <= n,
                best == -1 || 1 <= best <= 1000,
                best == -1 <==> !(exists |p: int, q: int|
                    0 <= p < i && 0 <= q < n && nums[p] > 0 && nums[q] == -nums[p]),
                best >= 1 ==> exists |p: int, q: int|
                    0 <= p < i && 0 <= q < n && nums[p] == best && nums[q] == -best,
                best >= 1 ==> forall |p: int, q: int|
                    0 <= p < i && 0 <= q < n && nums[p] > 0 && nums[q] == -nums[p]
                        ==> nums[p] <= best,
            decreases n - i,
        {
            let current = nums[i];
            if current > 0 {
                let mut found = false;
                let mut j: usize = 0;
                while j < n
                    invariant
                        n == nums.len(),
                        1 <= n <= 1000,
                        forall |k: int| 0 <= k < nums.len() ==> -1000 <= #[trigger] nums[k] <= 1000,
                        forall |k: int| 0 <= k < nums.len() ==> nums[k] != 0,
                        0 <= i < n,
                        current == nums[i as int],
                        1 <= current <= 1000,
                        0 <= j <= n,
                        found ==> exists |m: int| 0 <= m < j && nums[m] == -current,
                        !found ==> forall |m: int| 0 <= m < j ==> nums[m] != -current,
                    decreases n - j,
                {
                    if nums[j] == -current {
                        found = true;
                    }
                    j += 1;
                }

                proof {
                    assert(found == (exists |m: int| 0 <= m < n && nums[m] == -current)) by {
                        if found {
                            let m = choose |m: int| 0 <= m < j && nums[m] == -current;
                            assert(0 <= m < n);
                        } else {
                            assert(j == n);
                            assert(!(exists |m: int| 0 <= m < n && nums[m] == -current)) by {
                                if exists |m: int| 0 <= m < n && nums[m] == -current {
                                    let m = choose |m: int| 0 <= m < n && nums[m] == -current;
                                    assert(0 <= m < j);
                                    assert(nums[m] != -current);
                                }
                            }
                        }
                    }
                }

                let prev_best = best;
                proof {
                    assert(prev_best == -1 <==> !(exists |p: int, q: int|
                        0 <= p < i && 0 <= q < n && nums[p] > 0 && nums[q] == -nums[p]));
                    assert(prev_best >= 1 ==> exists |p: int, q: int|
                        0 <= p < i && 0 <= q < n && nums[p] == prev_best && nums[q] == -prev_best);
                    assert(prev_best >= 1 ==> forall |p: int, q: int|
                        0 <= p < i && 0 <= q < n && nums[p] > 0 && nums[q] == -nums[p]
                            ==> nums[p] <= prev_best);
                }

                if found && current > best {
                    best = current;
                }

                proof {
                    if best == -1 {
                        assert(prev_best == -1);
                        assert(!found);
                        assert forall |p: int, q: int|
                            0 <= p < i + 1 && 0 <= q < n && nums[p] > 0 && nums[q] == -nums[p]
                        implies false by {
                            if p < i {
                                assert(!(exists |pp: int, qq: int|
                                    0 <= pp < i && 0 <= qq < n && nums[pp] > 0 && nums[qq] == -nums[pp]));
                            } else {
                                assert(p == i as int);
                                assert(nums[p] == current);
                                assert(found == (exists |m: int| 0 <= m < n && nums[m] == -current));
                                assert(found);
                            }
                        }
                    } else {
                        assert(best >= 1);
                        assert(prev_best <= best);
                        if found && current > prev_best {
                            assert(best == current);
                            assert(exists |p: int, q: int|
                                0 <= p < i + 1 && 0 <= q < n && nums[p] == best && nums[q] == -best) by {
                                let q = choose |q: int| 0 <= q < n && nums[q] == -current;
                                assert(0 <= i as int);
                                assert((i as int) < ((i + 1) as int));
                                assert(nums[i as int] == best);
                                assert(nums[q] == -best);
                            }
                        } else {
                            assert(prev_best >= 1);
                            assert(best == prev_best);
                            assert(exists |p: int, q: int|
                                0 <= p < i + 1 && 0 <= q < n && nums[p] == best && nums[q] == -best) by {
                                assert(exists |p: int, q: int|
                                    0 <= p < i && 0 <= q < n && nums[p] == prev_best && nums[q] == -prev_best);
                            }
                        }
                        assert forall |p: int, q: int|
                            0 <= p < i + 1 && 0 <= q < n && nums[p] > 0 && nums[q] == -nums[p]
                        implies nums[p] <= best by {
                            if p < i {
                                if prev_best == -1 {
                                    assert(!(exists |pp: int, qq: int|
                                        0 <= pp < i && 0 <= qq < n && nums[pp] > 0 && nums[qq] == -nums[pp]));
                                } else {
                                    assert(nums[p] <= prev_best);
                                    assert(prev_best <= best);
                                }
                            } else {
                                assert(p == i as int);
                                assert(nums[p] == current);
                                if exists |m: int| 0 <= m < n && nums[m] == -current {
                                    if found && current > prev_best {
                                        assert(best == current);
                                    } else {
                                        assert(current <= prev_best);
                                        assert(prev_best == best);
                                    }
                                } else {
                                    assert(found == (exists |m: int| 0 <= m < n && nums[m] == -current));
                                    assert(found);
                                }
                            }
                        }
                    }
                }
            }
            i += 1;
        }

        proof {
            if best == -1 {
                assert(!(exists |p: int, q: int|
                    0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] > 0 && nums[q] == -nums[p]));
            } else {
                assert(best >= 1);
                assert(exists |p: int, q: int|
                    0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] == best && nums[q] == -best);
                assert forall |p: int, q: int|
                    0 <= p < nums.len() && 0 <= q < nums.len() && nums[p] > 0 && nums[q] == -nums[p]
                implies nums[p] <= best by {
                }
            }
        }

        best
    }
}

}
