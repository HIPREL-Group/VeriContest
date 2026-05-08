use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn all_ge_k(nums: Seq<i32>, k: int) -> bool {
        forall |i: int| 0 <= i < nums.len() ==> nums[i] as int >= k
    }

    pub open spec fn value_present(nums: Seq<i32>, v: int) -> bool {
        exists |i: int| 0 <= i < nums.len() && nums[i] as int == v
    }

    pub open spec fn count_distinct_in_range(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start
    {
        if start >= end {
            0
        } else {
            (if Self::value_present(nums, start) { 1int } else { 0int })
                + Self::count_distinct_in_range(nums, start + 1, end)
        }
    }

    proof fn lemma_count_extend(nums: Seq<i32>, start: int, end: int)
        requires
            start <= end <= 101,
        ensures
            Self::count_distinct_in_range(nums, start, end + 1)
                == Self::count_distinct_in_range(nums, start, end)
                    + (if Self::value_present(nums, end) { 1int } else { 0int }),
        decreases end - start,
    {
        if start == end {
            assert(Self::count_distinct_in_range(nums, start + 1, end + 1) == 0);
        } else {
            Self::lemma_count_extend(nums, start + 1, end);
        }
    }

    proof fn lemma_count_bounded(nums: Seq<i32>, start: int, end: int)
        requires
            start <= end <= 101,
        ensures
            0 <= Self::count_distinct_in_range(nums, start, end) <= end - start,
        decreases end - start,
    {
        if start >= end {
        } else {
            Self::lemma_count_bounded(nums, start + 1, end);
        }
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            -1 <= res <= 100,
            Self::all_ge_k(nums@, k as int) ==> res as int == Self::count_distinct_in_range(nums@, k as int + 1, 101),
            !Self::all_ge_k(nums@, k as int) ==> res == -1,
    {
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                1 <= nums.len() <= 100,
                forall |t: int| 0 <= t < nums.len() ==> 1 <= #[trigger] nums[t] <= 100,
                1 <= k <= 100,
                0 <= i <= nums.len(),
                forall |t: int| 0 <= t < i as int ==> nums@[t] as int >= k as int,
            decreases nums.len() - i,
        {
            let x = nums[i];
            if x < k {
                proof {
                    assert(!Self::all_ge_k(nums@, k as int)) by {
                        if Self::all_ge_k(nums@, k as int) {
                            assert(nums@[i as int] as int >= k as int);
                            assert(nums@[i as int] == x);
                            assert(x < k);
                            assert(false);
                        }
                    }
                }
                return -1;
            }
            i = i + 1;
        }

        proof {
            assert(Self::all_ge_k(nums@, k as int)) by {
                assert(forall |t: int| 0 <= t < nums.len() ==> nums@[t] as int >= k as int) by {
                    assert(i == nums.len());
                    assert(forall |t: int| 0 <= t < i as int ==> nums@[t] as int >= k as int);
                }
            }
        }

        let mut ans: i32 = 0;
        let mut value: i32 = k + 1;
        while value <= 100
            invariant
                1 <= nums.len() <= 100,
                forall |t: int| 0 <= t < nums.len() ==> 1 <= #[trigger] nums[t] <= 100,
                1 <= k <= 100,
                Self::all_ge_k(nums@, k as int),
                k + 1 <= value <= 101,
                0 <= ans <= 100,
                ans as int == Self::count_distinct_in_range(nums@, k as int + 1, value as int),
            decreases 101 - value,
        {
            let mut found: bool = false;
            let mut j: usize = 0;
            while j < nums.len()
                invariant
                    1 <= nums.len() <= 100,
                    forall |t: int| 0 <= t < nums.len() ==> 1 <= #[trigger] nums[t] <= 100,
                    k + 1 <= value <= 100,
                    0 <= j <= nums.len(),
                    found ==> (exists |t: int| 0 <= t < j as int && nums@[t] as int == value as int),
                    !found ==> (forall |t: int| 0 <= t < j as int ==> nums@[t] as int != value as int),
                decreases nums.len() - j,
            {
                if nums[j] == value {
                    found = true;
                }
                j = j + 1;
            }

            proof {
                assert(j == nums.len());
                if found {
                    let t = choose |t: int| 0 <= t < j as int && nums@[t] as int == value as int;
                    assert(0 <= t < nums.len());
                    assert(Self::value_present(nums@, value as int));
                } else {
                    assert(!Self::value_present(nums@, value as int)) by {
                        if Self::value_present(nums@, value as int) {
                            let t = choose |t: int| 0 <= t < nums.len() && nums@[t] as int == value as int;
                            assert(0 <= t < j as int);
                            assert(nums@[t] as int != value as int);
                            assert(false);
                        }
                    }
                }
                Self::lemma_count_extend(nums@, k as int + 1, value as int);
            }

            let old_ans = ans;
            if found {
                ans = ans + 1;
            }

            proof {
                if found {
                    assert(Self::value_present(nums@, value as int));
                    assert(old_ans as int == Self::count_distinct_in_range(nums@, k as int + 1, value as int));
                    assert(ans == old_ans + 1);
                    assert(Self::count_distinct_in_range(nums@, k as int + 1, value as int + 1)
                        == Self::count_distinct_in_range(nums@, k as int + 1, value as int) + 1);
                    assert(ans as int == Self::count_distinct_in_range(nums@, k as int + 1, value as int + 1));
                } else {
                    assert(!Self::value_present(nums@, value as int));
                    assert(ans == old_ans);
                    assert(Self::count_distinct_in_range(nums@, k as int + 1, value as int + 1)
                        == Self::count_distinct_in_range(nums@, k as int + 1, value as int));
                    assert(ans as int == Self::count_distinct_in_range(nums@, k as int + 1, value as int + 1));
                }
            }

            proof {
                Self::lemma_count_bounded(nums@, k as int + 1, value as int + 1);
                assert(ans as int == Self::count_distinct_in_range(nums@, k as int + 1, value as int + 1));
                assert(0 <= ans as int <= (value as int + 1) - (k as int + 1));
                assert((value as int + 1) - (k as int + 1) <= 100);
                assert(0 <= ans <= 100);
            }

            value = value + 1;
        }

        proof {
            Self::lemma_count_bounded(nums@, k as int + 1, 101);
            assert(ans as int == Self::count_distinct_in_range(nums@, k as int + 1, 101));
            assert(ans as int <= 101 - (k as int + 1));
            assert(ans <= 100);
        }

        ans
    }
}

}
