use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains(nums: Seq<i32>, value: int) -> bool {
        exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] as int == value
    }

    pub open spec fn seq_sum(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn smallest_absent(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            1 <= res,
            (res as int) * nums.len() as int > Self::seq_sum(nums@, nums.len() as int),
            !Self::contains(nums@, res as int),
            forall |x: int| 1 <= x < res as int
                && x * nums.len() as int > Self::seq_sum(nums@, nums.len() as int)
                ==> Self::contains(nums@, x),
    {
        let n_usize = nums.len();
        let n = n_usize as i32;

        let mut sum: i32 = 0;
        let mut i: usize = 0;
        while i < n_usize
            invariant
                0 <= i <= n_usize,
                n_usize == nums.len(),
                n as int == n_usize as int,
                1 <= n as int <= 100,
                forall |k: int| 0 <= k < nums.len() ==> -100 <= #[trigger] nums[k] <= 100,
                sum as int == Self::seq_sum(nums@, i as int),
                -100 * i as int <= sum as int,
                sum as int <= 100 * i as int,
            decreases n_usize - i,
        {
            sum += nums[i];
            proof {
                assert(Self::seq_sum(nums@, (i + 1) as int) == Self::seq_sum(nums@, i as int) + nums@[i as int] as int);
            }
            i += 1;
        }

        let mut candidate: i32 = 1;
        let mut candidate_times_n: i32 = n;
        while candidate < 101
            invariant
                n_usize == nums.len(),
                n as int == n_usize as int,
                1 <= n as int <= 100,
                forall |k: int| 0 <= k < nums.len() ==> -100 <= #[trigger] nums[k] <= 100,
                sum as int == Self::seq_sum(nums@, nums.len() as int),
                -100 * n as int <= sum as int,
                sum as int <= 100 * n as int,
                1 <= candidate <= 101,
                candidate_times_n as int == candidate as int * n as int,
                n as int <= candidate_times_n as int <= 10100,
                forall |x: int| 1 <= x < candidate as int ==> x * n as int <= sum as int || #[trigger] Self::contains(nums@, x),
            decreases 101 - candidate as int,
        {
            let mut exists = false;
            let mut j: usize = 0;
            while j < n_usize && !exists
                invariant
                    0 <= j <= n_usize,
                    n_usize == nums.len(),
                    !exists ==> forall |t: int| 0 <= t < j as int ==> nums@[t] as int != candidate as int,
                    exists ==> Self::contains(nums@, candidate as int),
                decreases n_usize - j,
            {
                if nums[j] == candidate {
                    exists = true;
                    proof {
                        assert(Self::contains(nums@, candidate as int)) by {
                            assert(0 <= j);
                            assert(j < n_usize);
                            assert(0 <= (j as int));
                            assert((j as int) < (n_usize as int));
                            assert(n_usize as int == nums.len());
                            assert(nums@[j as int] as int == candidate as int);
                        };
                    }
                }
                j += 1;
            }

            if candidate_times_n > sum && !exists {
                proof {
                    assert(j == n_usize);
                    assert forall |t: int| 0 <= t < nums.len() implies nums@[t] as int != candidate as int by {
                    };
                    assert(!Self::contains(nums@, candidate as int));
                    assert(candidate as int * n as int > sum as int);
                    assert forall |x: int| 1 <= x < candidate as int
                        && x * nums.len() as int > Self::seq_sum(nums@, nums.len() as int)
                        implies Self::contains(nums@, x) by {
                        assert(x * n as int > sum as int);
                        assert(x * n as int <= sum as int || Self::contains(nums@, x));
                        if x * n as int <= sum as int {
                            assert(false);
                        }
                    };
                }
                return candidate;
            }

            proof {
                assert forall |x: int| 1 <= x < candidate as int + 1
                    implies x * n as int <= sum as int || #[trigger] Self::contains(nums@, x)
                by {
                    if x < candidate as int {
                    } else {
                        assert(x == candidate as int);
                        if candidate_times_n > sum {
                            assert(exists);
                            assert(Self::contains(nums@, candidate as int));
                        } else {
                            assert(x * n as int == candidate_times_n as int);
                            assert(x * n as int <= sum as int);
                        }
                    }
                };
                assert(candidate < 101);
                assert(candidate_times_n as int <= 10000) by (nonlinear_arith)
                    requires
                        candidate_times_n as int == candidate as int * n as int,
                        candidate as int <= 100,
                        n as int <= 100,
                        n as int >= 1,
                {};
                assert(candidate_times_n as int + n as int <= 10100);
            }
            let ghost old_candidate = candidate as int;
            let ghost old_candidate_times_n = candidate_times_n as int;
            candidate += 1;
            candidate_times_n += n;
            proof {
                assert(candidate as int == old_candidate + 1);
                assert(candidate_times_n as int == old_candidate_times_n + n as int);
                assert(old_candidate_times_n == old_candidate * n as int);
                assert(candidate_times_n as int == candidate as int * n as int) by (nonlinear_arith)
                    requires
                        candidate as int == old_candidate + 1,
                        candidate_times_n as int == old_candidate_times_n + n as int,
                        old_candidate_times_n == old_candidate * n as int,
                {};
                assert(candidate_times_n as int >= n as int);
                assert(candidate_times_n as int <= 10100);
            }
        }

        proof {
            assert(candidate == 101);
            assert forall |t: int| 0 <= t < nums.len() implies nums@[t] as int != 101 by {
                assert(nums@[t] <= 100);
            };
            assert(!Self::contains(nums@, 101));
            assert(101 * n as int > sum as int) by (nonlinear_arith)
                requires
                    sum as int <= 100 * n as int,
                    1 <= n as int,
                {};
            assert forall |x: int| 1 <= x < 101
                && x * nums.len() as int > Self::seq_sum(nums@, nums.len() as int)
                implies Self::contains(nums@, x) by {
                assert(x * n as int > sum as int);
                assert(x * n as int <= sum as int || Self::contains(nums@, x));
                if x * n as int <= sum as int {
                    assert(false);
                }
            };
        }

        101
    }
}

}
