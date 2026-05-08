use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain_triplet(nums: Seq<i32>, i: int, j: int, k: int) -> bool {
        &&& 0 <= i < j < k < nums.len()
        &&& nums[i] < nums[j]
        &&& nums[k] < nums[j]
    }

    pub open spec fn triplet_sum(nums: Seq<i32>, i: int, j: int, k: int) -> int {
        nums[i] as int + nums[j] as int + nums[k] as int
    }

    pub fn minimum_sum(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
        ensures
            result == -1 ==> forall |i: int, j: int, k: int|
                !Self::is_mountain_triplet(nums@, i, j, k),
            result != -1 ==> exists |i: int, j: int, k: int|
                Self::is_mountain_triplet(nums@, i, j, k)
                && result as int == Self::triplet_sum(nums@, i, j, k),
            result != -1 ==> forall |i: int, j: int, k: int|
                Self::is_mountain_triplet(nums@, i, j, k)
                ==> result as int <= Self::triplet_sum(nums@, i, j, k),
    {
        let n = nums.len();

        let mut left_idx: Vec<usize> = Vec::new();
        left_idx.push(0);
        let mut p: usize = 1;
        while p < n
            invariant
                n == nums.len(),
                3 <= n <= 100000,
                1 <= p <= n,
                left_idx.len() == p,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
                forall |j: int| 0 <= j < p ==> 0 <= #[trigger] left_idx[j] <= j,
                forall |j: int, t: int|
                    0 <= j < p && 0 <= t <= j ==> nums[#[trigger] left_idx[j] as int] <= #[trigger] nums[t],
            decreases n - p,
        {
            let mut best = left_idx[p - 1];
            if nums[p] < nums[best] {
                best = p;
                proof {
                    assert forall |t: int| 0 <= t <= p as int implies nums[best as int] <= #[trigger] nums[t] by {
                        if t == p as int {
                        } else {
                            assert(0 <= t <= p as int - 1);
                            assert(nums[left_idx[p as int - 1] as int] <= nums[t]);
                            assert(nums[best as int] == nums[p as int]);
                            assert(nums[p as int] < nums[left_idx[p as int - 1] as int]);
                        }
                    };
                }
            } else {
                proof {
                    assert forall |t: int| 0 <= t <= p as int implies nums[best as int] <= #[trigger] nums[t] by {
                        if t == p as int {
                            assert(nums[p as int] >= nums[best as int]);
                        } else {
                            assert(0 <= t <= p as int - 1);
                            assert(nums[left_idx[p as int - 1] as int] <= nums[t]);
                            assert(best == left_idx[p as int - 1]);
                        }
                    };
                }
            }
            left_idx.push(best);
            p += 1;
        }

        let mut right_idx: Vec<usize> = Vec::new();
        let mut q: usize = 0;
        while q < n
            invariant
                n == nums.len(),
                3 <= n <= 100000,
                0 <= q <= n,
                right_idx.len() == q,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
                forall |j: int| 0 <= j < q ==> #[trigger] right_idx[j] == j,
            decreases n - q,
        {
            right_idx.push(q);
            q += 1;
        }

        let mut q: usize = n - 1;
        while q > 0
            invariant
                n == nums.len(),
                3 <= n <= 100000,
                0 <= q < n,
                right_idx.len() == n,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
                forall |j: int| 0 <= j < q ==> #[trigger] right_idx[j] == j,
                forall |j: int| q <= j < n ==> j <= #[trigger] right_idx[j] < n,
                forall |j: int, t: int|
                    q <= j < n && j <= t < n ==> nums[#[trigger] right_idx[j] as int] <= #[trigger] nums[t],
            decreases q,
        {
            let prev = q - 1;
            let mut best = right_idx[q];
            if nums[prev] <= nums[best] {
                best = prev;
                proof {
                    assert forall |t: int| prev as int <= t < n as int implies nums[best as int] <= #[trigger] nums[t] by {
                        if t == prev as int {
                        } else {
                            assert(q as int <= t < n as int);
                            assert(nums[right_idx[q as int] as int] <= nums[t]);
                            assert(nums[best as int] == nums[prev as int]);
                            assert(nums[prev as int] <= nums[right_idx[q as int] as int]);
                        }
                    };
                }
            } else {
                proof {
                    assert forall |t: int| prev as int <= t < n as int implies nums[best as int] <= #[trigger] nums[t] by {
                        if t == prev as int {
                            assert(nums[prev as int] > nums[best as int]);
                        } else {
                            assert(q as int <= t < n as int);
                            assert(nums[right_idx[q as int] as int] <= nums[t]);
                            assert(best == right_idx[q as int]);
                        }
                    };
                }
            }
            right_idx.set(prev, best);
            q -= 1;
        }

        let mut best_sum: i32 = 300000001;
        let ghost mut best_i: int = 0;
        let ghost mut best_j: int = 0;
        let ghost mut best_k: int = 0;
        let mut j: usize = 1;
        while j + 1 < n
            invariant
                n == nums.len(),
                3 <= n <= 100000,
                1 <= j <= n - 1,
                left_idx.len() == n,
                right_idx.len() == n,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
                forall |c: int| 0 <= c < n ==> 0 <= #[trigger] left_idx[c] <= c,
                forall |c: int, t: int|
                    0 <= c < n && 0 <= t <= c ==> nums[#[trigger] left_idx[c] as int] <= #[trigger] nums[t],
                forall |c: int| 0 <= c < n ==> c <= #[trigger] right_idx[c] < n,
                forall |c: int, t: int|
                    0 <= c < n && c <= t < n ==> nums[#[trigger] right_idx[c] as int] <= #[trigger] nums[t],
                0 < best_sum <= 300000001,
                best_sum == 300000001 ==> forall |i: int, c: int, k: int|
                    1 <= c < j ==> !Self::is_mountain_triplet(nums@, i, c, k),
                best_sum < 300000001 ==> Self::is_mountain_triplet(nums@, best_i, best_j, best_k),
                best_sum < 300000001 ==> 1 <= best_j < j,
                best_sum < 300000001 ==> best_sum as int == Self::triplet_sum(nums@, best_i, best_j, best_k),
                best_sum < 300000001 ==> forall |i: int, c: int, k: int|
                    1 <= c < j && Self::is_mountain_triplet(nums@, i, c, k)
                    ==> best_sum as int <= Self::triplet_sum(nums@, i, c, k),
            decreases n - 1 - j,
        {
            let left = left_idx[j - 1];
            let right = right_idx[j + 1];
            let old_best = best_sum;

            if nums[left] < nums[j] && nums[right] < nums[j] {
                let candidate = nums[left] + nums[j] + nums[right];
                proof {
                    assert(Self::is_mountain_triplet(nums@, left as int, j as int, right as int));
                    assert(candidate as int == Self::triplet_sum(nums@, left as int, j as int, right as int));
                    assert forall |i: int, k: int|
                        Self::is_mountain_triplet(nums@, i, j as int, k)
                        implies candidate as int <= Self::triplet_sum(nums@, i, j as int, k) by {
                        assert(0 <= i < j as int);
                        assert((j as int) < k);
                        assert(k < n as int);
                        assert(nums[left as int] <= nums[i]);
                        assert(nums[right as int] <= nums[k]);
                    };
                }
                if candidate < best_sum {
                    best_sum = candidate;
                    proof {
                        best_i = left as int;
                        best_j = j as int;
                        best_k = right as int;
                    }
                }
                proof {
                    assert(best_sum < 300000001);
                    assert forall |i: int, c: int, k: int|
                        1 <= c < j as int + 1 && Self::is_mountain_triplet(nums@, i, c, k)
                        implies best_sum as int <= Self::triplet_sum(nums@, i, c, k) by {
                        if c < j as int {
                            assert(old_best < 300000001);
                            assert(old_best as int <= Self::triplet_sum(nums@, i, c, k));
                            assert(best_sum <= old_best);
                        } else {
                            assert(c == j as int);
                            assert(candidate as int <= Self::triplet_sum(nums@, i, c, k));
                            if best_sum == old_best {
                                assert(old_best as int <= candidate as int);
                            } else {
                                assert(best_sum == candidate);
                            }
                        }
                    };
                }
            } else {
                proof {
                    assert forall |i: int, k: int| !Self::is_mountain_triplet(nums@, i, j as int, k) by {
                        if Self::is_mountain_triplet(nums@, i, j as int, k) {
                            if nums[left as int] >= nums[j as int] {
                                assert(0 <= i < j as int);
                                assert(nums[left as int] <= nums[i]);
                                assert(nums[i] < nums[j as int]);
                                assert(false);
                            } else {
                                assert(nums[right as int] >= nums[j as int]);
                                assert((j as int) < k);
                                assert(k < n as int);
                                assert(nums[right as int] <= nums[k]);
                                assert(nums[k] < nums[j as int]);
                                assert(false);
                            }
                        }
                    };
                }
            }

            proof {
                if best_sum == 300000001 {
                    assert forall |i: int, c: int, k: int|
                        1 <= c < j as int + 1 implies !Self::is_mountain_triplet(nums@, i, c, k) by {
                        if c < j as int {
                            assert(!Self::is_mountain_triplet(nums@, i, c, k));
                        } else {
                            assert(j as int <= c);
                            assert(c < j as int + 1);
                            assert(c == j as int);
                            assert(!Self::is_mountain_triplet(nums@, i, c, k));
                        }
                    };
                } else {
                    assert(Self::is_mountain_triplet(nums@, best_i, best_j, best_k));
                    assert(1 <= best_j <= j as int);
                    assert(best_sum as int == Self::triplet_sum(nums@, best_i, best_j, best_k));
                    assert forall |i: int, c: int, k: int|
                        1 <= c < j as int + 1 && Self::is_mountain_triplet(nums@, i, c, k)
                        implies best_sum as int <= Self::triplet_sum(nums@, i, c, k) by {
                        if c < j as int {
                            if old_best < 300000001 {
                                assert(old_best as int <= Self::triplet_sum(nums@, i, c, k));
                                assert(best_sum <= old_best);
                            }
                        }
                    };
                }
            }

            j += 1;
        }

        if best_sum == 300000001 {
            proof {
                assert forall |i: int, c: int, k: int|
                    !Self::is_mountain_triplet(nums@, i, c, k) by {
                    if Self::is_mountain_triplet(nums@, i, c, k) {
                        assert(1 <= c < n as int - 1);
                        assert(c < j as int);
                    }
                };
            }
            -1
        } else {
            proof {
                assert(exists |i: int, c: int, k: int|
                    Self::is_mountain_triplet(nums@, i, c, k)
                    && best_sum as int == Self::triplet_sum(nums@, i, c, k));
                assert forall |i: int, c: int, k: int|
                    Self::is_mountain_triplet(nums@, i, c, k)
                    implies best_sum as int <= Self::triplet_sum(nums@, i, c, k) by {
                    assert(1 <= c < n as int - 1);
                    assert(c < j as int);
                };
            }
            best_sum
        }
    }
}

}
