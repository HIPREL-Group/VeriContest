use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inc_prefix(nums: Seq<i32>, p: int) -> bool {
        0 < p && p < nums.len()
        && forall|j: int| 0 <= j && j < p ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub open spec fn dec_mid(nums: Seq<i32>, p: int, q: int) -> bool {
        0 < p && p < q && q < nums.len()
        && forall|j: int| p <= j && j < q ==> #[trigger] nums[j] > nums[j + 1]
    }

    pub open spec fn inc_suffix(nums: Seq<i32>, q: int) -> bool {
        0 <= q && q < nums.len() - 1
        && forall|j: int| q <= j && j < nums.len() - 1 ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub open spec fn trionic_at(nums: Seq<i32>, p: int, q: int) -> bool {
        0 < p && p < q && q < nums.len() - 1
        && Self::inc_prefix(nums, p)
        && Self::dec_mid(nums, p, q)
        && Self::inc_suffix(nums, q)
    }

    pub open spec fn has_trionic(nums: Seq<i32>) -> bool {
        exists|p: int, q: int| #[trigger] Self::trionic_at(nums, p, q)
    }

    fn check_prefix_inc(nums: &Vec<i32>, p: usize) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            0 < p < nums.len(),
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::inc_prefix(nums@, p as int),
    {
        let n = nums.len();
        let mut i: usize = 0;
        while i < p
            invariant
                n == nums.len(),
                3 <= n <= 100,
                0 < p < n,
                0 <= i <= p,
                forall|k: int| 0 <= k && k < n ==> -1000 <= #[trigger] nums[k] <= 1000,
                forall|j: int| 0 <= j && j < (i as int) ==> #[trigger] nums@[j] < nums@[j + 1],
            decreases p - i,
        {
            if nums[i] >= nums[i + 1] {
                proof {
                    assert(!Self::inc_prefix(nums@, p as int)) by {
                        if Self::inc_prefix(nums@, p as int) {
                            assert(0 <= i as int && (i as int) < (p as int));
                            assert(nums@[i as int] < nums@[(i + 1) as int]);
                            assert(nums@[i as int] >= nums@[(i + 1) as int]);
                            assert(false);
                        }
                    };
                }
                return false;
            }
            i += 1;
        }
        proof {
            assert(i == p);
            assert(Self::inc_prefix(nums@, p as int));
        }
        true
    }

    fn check_mid_dec(nums: &Vec<i32>, p: usize, q: usize) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            0 < p < q < nums.len(),
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::dec_mid(nums@, p as int, q as int),
    {
        let n = nums.len();
        let mut i: usize = p;
        while i < q
            invariant
                n == nums.len(),
                3 <= n <= 100,
                0 < p < q < n,
                p <= i <= q,
                forall|k: int| 0 <= k && k < n ==> -1000 <= #[trigger] nums[k] <= 1000,
                forall|j: int| p as int <= j && j < (i as int) ==> #[trigger] nums@[j] > nums@[j + 1],
            decreases q - i,
        {
            if nums[i] <= nums[i + 1] {
                proof {
                    assert(!Self::dec_mid(nums@, p as int, q as int)) by {
                        if Self::dec_mid(nums@, p as int, q as int) {
                            assert(p as int <= i as int && (i as int) < (q as int));
                            assert(nums@[i as int] > nums@[(i + 1) as int]);
                            assert(nums@[i as int] <= nums@[(i + 1) as int]);
                            assert(false);
                        }
                    };
                }
                return false;
            }
            i += 1;
        }
        proof {
            assert(i == q);
            assert(Self::dec_mid(nums@, p as int, q as int));
        }
        true
    }

    fn check_suffix_inc(nums: &Vec<i32>, q: usize) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            0 <= q < nums.len() - 1,
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::inc_suffix(nums@, q as int),
    {
        let n = nums.len();
        let mut i: usize = q;
        while i + 1 < n
            invariant
                n == nums.len(),
                3 <= n <= 100,
                0 <= q < n - 1,
                q <= i < n,
                forall|k: int| 0 <= k && k < n ==> -1000 <= #[trigger] nums[k] <= 1000,
                forall|j: int| q as int <= j && j < (i as int) ==> #[trigger] nums@[j] < nums@[j + 1],
            decreases n - i,
        {
            if nums[i] >= nums[i + 1] {
                proof {
                    assert(!Self::inc_suffix(nums@, q as int)) by {
                        if Self::inc_suffix(nums@, q as int) {
                            assert(q as int <= i as int && (i as int) < (n as int) - 1);
                            assert(nums@[i as int] < nums@[(i + 1) as int]);
                            assert(nums@[i as int] >= nums@[(i + 1) as int]);
                            assert(false);
                        }
                    };
                }
                return false;
            }
            i += 1;
        }
        proof {
            assert(i == n - 1);
            assert(Self::inc_suffix(nums@, q as int));
        }
        true
    }

    fn check_pq(nums: &Vec<i32>, p: usize, q: usize) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            0 < p < q < nums.len() - 1,
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::trionic_at(nums@, p as int, q as int),
    {
        let a = Self::check_prefix_inc(nums, p);
        if !a {
            proof {
                assert(!Self::trionic_at(nums@, p as int, q as int)) by {
                    if Self::trionic_at(nums@, p as int, q as int) {
                        assert(Self::inc_prefix(nums@, p as int));
                        assert(false);
                    }
                };
            }
            return false;
        }

        let b = Self::check_mid_dec(nums, p, q);
        if !b {
            proof {
                assert(!Self::trionic_at(nums@, p as int, q as int)) by {
                    if Self::trionic_at(nums@, p as int, q as int) {
                        assert(Self::dec_mid(nums@, p as int, q as int));
                        assert(false);
                    }
                };
            }
            return false;
        }

        let c = Self::check_suffix_inc(nums, q);
        if !c {
            proof {
                assert(!Self::trionic_at(nums@, p as int, q as int)) by {
                    if Self::trionic_at(nums@, p as int, q as int) {
                        assert(Self::inc_suffix(nums@, q as int));
                        assert(false);
                    }
                };
            }
            return false;
        }

        proof {
            assert(Self::inc_prefix(nums@, p as int));
            assert(Self::dec_mid(nums@, p as int, q as int));
            assert(Self::inc_suffix(nums@, q as int));
            assert(Self::trionic_at(nums@, p as int, q as int));
        }
        true
    }

    pub fn is_trionic(nums: Vec<i32>) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::has_trionic(nums@),
    {
        let n = nums.len();
        if n < 4 {
            proof {
                assert forall|p: int, q: int| #[trigger] Self::trionic_at(nums@, p, q) implies false by {
                    assert(0 < p && p < q && q < (n as int) - 1);
                    assert(2 <= q);
                    assert(q + 2 <= n as int);
                    assert((n as int) < 4);
                    assert(false);
                };
                assert(!Self::has_trionic(nums@));
            }
            return false;
        }

        let mut p: usize = 1;
        while p + 2 < n
            invariant
                n == nums.len(),
                4 <= n <= 100,
                1 <= p <= n - 2,
                forall|i: int| 0 <= i && i < n ==> -1000 <= #[trigger] nums[i] <= 1000,
                forall|pp: int, qq: int|
                    1 <= pp && pp < p as int && pp < qq && qq < (n as int) - 1
                        && #[trigger] Self::trionic_at(nums@, pp, qq) ==> false,
            decreases n - p,
        {
            let mut q: usize = p + 1;
            while q + 1 < n
                invariant
                    n == nums.len(),
                    4 <= n <= 100,
                    1 <= p < n - 1,
                    p + 1 <= q <= n - 1,
                    forall|i: int| 0 <= i && i < n ==> -1000 <= #[trigger] nums[i] <= 1000,
                    forall|pp: int, qq: int|
                        1 <= pp && pp < p as int && pp < qq && qq < (n as int) - 1
                            && #[trigger] Self::trionic_at(nums@, pp, qq) ==> false,
                    forall|qq: int|
                        (p as int) < qq && qq < (q as int) && #[trigger] Self::trionic_at(nums@, p as int, qq)
                            ==> false,
                decreases n - q,
            {
                if Self::check_pq(&nums, p, q) {
                    proof {
                        assert(Self::trionic_at(nums@, p as int, q as int));
                        assert(Self::has_trionic(nums@)) by {
                            assert(Self::trionic_at(nums@, p as int, q as int));
                        };
                    }
                    return true;
                }

                proof {
                    assert(!Self::trionic_at(nums@, p as int, q as int));
                }

                let ghost q_before = q as int;
                q += 1;

                proof {
                    assert(q as int == q_before + 1);
                    assert forall|qq: int|
                        (p as int) < qq && qq < (q as int) && #[trigger] Self::trionic_at(nums@, p as int, qq)
                            implies false by {
                        if qq < q_before {
                            assert((p as int) < qq && qq < q_before);
                        } else {
                            assert(qq == q_before);
                            assert(!Self::trionic_at(nums@, p as int, qq));
                        }
                    };
                }
            }

            proof {
                assert(q == n - 1);
                assert forall|pp: int, qq: int|
                    1 <= pp && pp < (p + 1) as int && pp < qq && qq < (n as int) - 1
                        && #[trigger] Self::trionic_at(nums@, pp, qq) implies false by {
                    if pp < p as int {
                        assert(pp < p as int);
                    } else {
                        assert(pp == p as int);
                        assert((p as int) < qq && qq < (q as int));
                    }
                };
            }

            p += 1;
        }

        proof {
            assert(p == n - 2);
            assert forall|pp: int, qq: int| #[trigger] Self::trionic_at(nums@, pp, qq) implies false by {
                assert(0 < pp && pp < qq && qq < (n as int) - 1);
                assert(pp + 2 <= qq + 1);
                assert(qq + 1 < n as int);
                assert(pp + 2 < n as int);
                assert(pp < p as int);
            };
            assert(!Self::has_trionic(nums@));
        }

        false
    }
}

}
