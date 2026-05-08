use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_int(nums: Seq<i32>, value: int) -> bool {
        exists |i: int| 0 <= i < nums.len() && nums[i] as int == value
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn missing_multiple(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            result > 0,
            result as int % k as int == 0,
            !Self::contains_int(nums@, result as int),
            forall |q: int| q >= 1 && !Self::contains_int(nums@, #[trigger] (k as int * q)) ==> result as int <= k as int * q,
    {
        let n = nums.len();
        let mut t: i32 = 1;
        let mut candidate = k;

        while candidate <= 100
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
                1 <= k <= 100,
                1 <= t <= 101,
                1 <= candidate <= 200,
                candidate as int == k as int * t as int,
                forall |q: int| 1 <= q < t as int ==> #[trigger] Self::contains_int(nums@, k as int * q),
            decreases 101 - t as int,
        {
            let mut exists = false;
            let mut i: usize = 0;
            while i < n
                invariant
                    n == nums.len(),
                    0 <= i <= n,
                    candidate as int == k as int * t as int,
                    1 <= k <= 100,
                    1 <= t <= 101,
                    1 <= candidate <= 200,
                    forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100,
                    exists <==> exists |j: int| 0 <= j < i as int && nums[j] == candidate,
                decreases n - i,
            {
                if nums[i] == candidate {
                    exists = true;
                }
                i += 1;
            }

            proof {
                assert(i == n);
                assert(exists <==> exists |j: int| 0 <= j < n as int && nums[j] == candidate);
            }

            if !exists {
                proof {
                    assert(!(exists |j: int| 0 <= j < n as int && nums[j] == candidate));
                    assert(!Self::contains_int(nums@, candidate as int)) by {
                        if Self::contains_int(nums@, candidate as int) {
                            let j = choose |j: int| 0 <= j < nums.len() && nums[j] as int == candidate as int;
                            assert(j < n as int);
                            assert(nums[j] == candidate);
                            assert(exists |x: int| 0 <= x < n as int && nums[x] == candidate);
                            assert(false);
                        }
                    };
                    assert(candidate > 0);
                    assert(candidate as int % k as int == 0) by (nonlinear_arith)
                        requires
                            candidate as int == k as int * t as int,
                            k as int > 0,
                    {
                    }
                    assert forall |q: int| q >= 1 && !Self::contains_int(nums@, #[trigger] (k as int * q))
                        implies candidate as int <= k as int * q
                    by {
                        if q < t as int {
                            assert(1 <= q < t as int);
                            assert(Self::contains_int(nums@, k as int * q));
                            assert(false);
                        } else {
                            assert(candidate as int <= k as int * q) by (nonlinear_arith)
                                requires
                                    q >= t as int,
                                    candidate as int == k as int * t as int,
                                    k as int > 0,
                            {
                            }
                        }
                    };
                }
                return candidate;
            }

            let ghost old_t = t;
            let ghost old_candidate = candidate;
            proof {
                let j = choose |j: int| 0 <= j < n as int && nums[j] == old_candidate;
                assert(nums[j] as int == old_candidate as int);
                assert(Self::contains_int(nums@, old_candidate as int));
                assert(Self::contains_int(nums@, k as int * old_t as int));
                assert(old_candidate <= 100);
                assert(old_t <= 100) by (nonlinear_arith)
                    requires
                        old_candidate as int == k as int * old_t as int,
                        old_candidate <= 100,
                        k as int >= 1,
                {
                }
            }

            candidate = candidate + k;
            t = t + 1;

            proof {
                assert(t as int == old_t as int + 1);
                assert(candidate as int == old_candidate as int + k as int);
                assert(1 <= t <= 101) by (nonlinear_arith)
                    requires
                        1 <= old_t <= 100,
                        t as int == old_t as int + 1,
                {
                }
                assert(1 <= candidate <= 200) by (nonlinear_arith)
                    requires
                        1 <= old_candidate <= 100,
                        1 <= k <= 100,
                        candidate as int == old_candidate as int + k as int,
                {
                }
                assert(old_candidate as int == k as int * old_t as int);
                assert(candidate as int == k as int * t as int) by (nonlinear_arith)
                    requires
                        candidate as int == old_candidate as int + k as int,
                        t as int == old_t as int + 1,
                        old_candidate as int == k as int * old_t as int,
                {
                }
                assert forall |q: int| 1 <= q < t as int implies #[trigger] Self::contains_int(nums@, k as int * q) by {
                    if q < old_t as int {
                        assert(1 <= q < old_t as int);
                    } else {
                        assert(q == old_t as int);
                        assert(Self::contains_int(nums@, k as int * old_t as int));
                    }
                };
            }
        }

        proof {
            assert(candidate as int > 100);
            assert(!Self::contains_int(nums@, candidate as int)) by {
                if Self::contains_int(nums@, candidate as int) {
                    let j = choose |j: int| 0 <= j < nums.len() && nums[j] as int == candidate as int;
                    assert(nums[j] as int <= 100);
                    assert(candidate as int > 100);
                    assert(false);
                }
            };
            assert(candidate > 0);
            assert(candidate as int % k as int == 0) by (nonlinear_arith)
                requires
                    candidate as int == k as int * t as int,
                    k as int > 0,
            {
            }
            assert forall |q: int| q >= 1 && !Self::contains_int(nums@, #[trigger] (k as int * q))
                implies candidate as int <= k as int * q
            by {
                if q < t as int {
                    assert(1 <= q < t as int);
                    assert(Self::contains_int(nums@, k as int * q));
                    assert(false);
                } else {
                    assert(candidate as int <= k as int * q) by (nonlinear_arith)
                        requires
                            q >= t as int,
                            candidate as int == k as int * t as int,
                            k as int > 0,
                    {
                    }
                }
            };
        }

        candidate
    }
}

}
