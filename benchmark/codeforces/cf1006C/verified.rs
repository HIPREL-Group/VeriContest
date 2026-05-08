use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i64>, end: int) -> int
        recommends 0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 { 0 }
        else { Self::prefix_sum(nums, end - 1) + nums[end - 1] as int }
    }

    pub open spec fn total_sum(nums: Seq<i64>) -> int {
        Self::prefix_sum(nums, nums.len() as int)
    }

    pub open spec fn valid_split(nums: Seq<i64>, a: int, j: int) -> bool {
        &&& 0 <= a <= j <= nums.len()
        &&& Self::prefix_sum(nums, a) == Self::total_sum(nums) - Self::prefix_sum(nums, j)
    }

    pub fn max_equal_outer_sum(nums: Vec<i64>) -> (result: i64)
        requires
            1 <= nums.len() <= 200_000,
            forall|k: int| 0 <= k < nums.len()
                ==> 1 <= #[trigger] nums[k] as int && (nums[k] as int) <= 1_000_000_000,
            Self::total_sum(nums@) <= i64::MAX,
        ensures
            forall|a: int, j: int|
                Self::valid_split(nums@, a, j)
                    ==> Self::prefix_sum(nums@, a) <= result as int,
            exists|a: int, j: int|
                Self::valid_split(nums@, a, j)
                    && Self::prefix_sum(nums@, a) == result as int,
    {
        let n = nums.len();
        let mut pref: Vec<i64> = Vec::new();
        pref.push(0);
        let mut i = 0usize;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                pref.len() == i + 1,
                forall|k: int| 0 <= k <= i as int
                    ==> #[trigger] pref[k] as int == Self::prefix_sum(nums@, k),
                forall|k: int| 0 <= k < nums.len()
                    ==> 1 <= #[trigger] nums[k] as int && (nums[k] as int) <= 1_000_000_000,
                Self::total_sum(nums@) <= i64::MAX,
            decreases n - i,
        {
            proof {
                lemma_prefix_sum_step(nums@, i as int);
                lemma_prefix_sum_le_total(nums@, i as int + 1);
                lemma_prefix_sum_nonneg_at(nums@, i as int + 1);
            }
            let next = pref[i] + nums[i];
            pref.push(next);
            i = i + 1;
            proof {
                assert forall|k: int| 0 <= k <= i as int
                    implies #[trigger] pref[k] as int == Self::prefix_sum(nums@, k) by {
                    if k < i as int {
                    } else {
                        assert(pref[k] == next);
                    }
                };
            }
        }
        let total = pref[n];
        proof {
            assert(total as int == Self::total_sum(nums@));
        }
        let mut left = 0usize;
        let mut right = n;
        let mut ans = 0i64;
        let ghost mut ga: int = 0;
        let ghost mut gj: int = n as int;
        proof {
            lemma_prefix_sum_nonneg(nums@);
            assert(total as int >= 0);
            assert(Self::prefix_sum(nums@, 0) == 0int) by {
                reveal_with_fuel(Solution::prefix_sum, 1);
            };
            assert(Self::valid_split(nums@, 0, n as int));
        }
        while left <= right
            invariant
                0 <= left <= n + 1,
                0 <= right <= n,
                left <= right + 1,
                n == nums.len(),
                pref.len() == n + 1,
                forall|k: int| 0 <= k <= n as int
                    ==> #[trigger] pref[k] as int == Self::prefix_sum(nums@, k),
                total as int == Self::total_sum(nums@),
                forall|k: int| 0 <= k < nums.len()
                    ==> 1 <= #[trigger] nums[k] as int,
                0 <= ans as int,
                ans as int <= total as int,
                Self::valid_split(nums@, ga, gj),
                Self::prefix_sum(nums@, ga) == ans as int,
                forall|a: int, j: int|
                    (Self::valid_split(nums@, a, j) && a < left as int)
                        ==> Self::prefix_sum(nums@, a) <= ans as int,
                forall|a: int, j: int|
                    (Self::valid_split(nums@, a, j) && j > right as int)
                        ==> Self::prefix_sum(nums@, a) <= ans as int,
            decreases right - left + 1,
        {
            proof {
                lemma_prefix_sum_le_total(nums@, right as int);
                assert(pref[right as int] as int <= total as int);
                lemma_prefix_sum_nonneg_at(nums@, right as int);
                assert(pref[right as int] as int >= 0);
            }
            let lsum = pref[left];
            let rsum = total - pref[right];
            proof {
                assert(lsum as int == Self::prefix_sum(nums@, left as int));
                assert(rsum as int >= 0);
            }
            if lsum < rsum {
                proof {
                    let left_int = left as int;
                    let right_int = right as int;
                    let lsum_int = lsum as int;
                    let rsum_int = rsum as int;
                    let ans_int = ans as int;
                    assert forall|a: int, j: int|
                        Self::valid_split(nums@, a, j) && a < left_int + 1
                        implies Self::prefix_sum(nums@, a) <= ans_int by {
                        if a < left_int {
                        } else {
                            if j > right_int {
                            } else {
                                lemma_prefix_sum_mono(nums@, j, right_int);
                                let psj = Self::prefix_sum(nums@, j);
                                let psr = Self::prefix_sum(nums@, right_int);
                                let ts = Self::total_sum(nums@);
                                assert(psj <= psr);
                                assert(ts - psj >= ts - psr);
                                assert(ts - psr == rsum_int);
                                assert(Self::prefix_sum(nums@, a) == ts - psj);
                                assert(Self::prefix_sum(nums@, a) >= rsum_int);
                                assert(Self::prefix_sum(nums@, a) == lsum_int);
                                assert(lsum_int < rsum_int);
                                assert(false);
                            }
                        }
                    };
                }
                left = left + 1;
            } else if lsum > rsum {
                proof {
                    let left_int = left as int;
                    let right_int = right as int;
                    let lsum_int = lsum as int;
                    let rsum_int = rsum as int;
                    let ans_int = ans as int;
                    if right == 0usize {
                        assert(pref[0] as int == Self::prefix_sum(nums@, 0));
                        reveal_with_fuel(Solution::prefix_sum, 1);
                        assert(rsum_int == total as int);
                        assert(left <= right);
                        assert(lsum_int == Self::prefix_sum(nums@, 0));
                        assert(lsum_int == 0);
                        lemma_prefix_sum_nonneg(nums@);
                        assert(false);
                    }
                    assert(right > 0usize);
                    assert forall|a: int, j: int|
                        Self::valid_split(nums@, a, j) && j > right_int - 1
                        implies Self::prefix_sum(nums@, a) <= ans_int by {
                        if j > right_int {
                        } else {
                            assert(j == right_int);
                            let ts = Self::total_sum(nums@);
                            let psr = Self::prefix_sum(nums@, right_int);
                            assert(Self::prefix_sum(nums@, a) == ts - psr);
                            assert(Self::prefix_sum(nums@, a) == rsum_int);
                            assert(rsum_int < lsum_int);
                            assert(Self::prefix_sum(nums@, a) < Self::prefix_sum(nums@, left_int));
                            lemma_prefix_sum_strict_mono_converse(nums@, a, left_int);
                            assert(a < left_int);
                        }
                    };
                }
                right = right - 1;
            } else {
                proof {
                    let left_int = left as int;
                    let right_int = right as int;
                    let ts = Self::total_sum(nums@);
                    let psr = Self::prefix_sum(nums@, right_int);
                    assert(Self::prefix_sum(nums@, left_int) == ts - psr);
                    assert(Self::valid_split(nums@, left_int, right_int));
                }
                if lsum > ans {
                    ans = lsum;
                    proof {
                        ga = left as int;
                        gj = right as int;
                    }
                }
                proof {
                    let left_int = left as int;
                    let right_int = right as int;
                    let lsum_int = lsum as int;
                    let cur_ans = ans as int;
                    assert forall|a: int, j: int|
                        Self::valid_split(nums@, a, j) && a < left_int + 1
                        implies Self::prefix_sum(nums@, a) <= cur_ans by {
                        if a < left_int {
                        } else {
                            if j > right_int {
                            } else {
                                if j < right_int {
                                    lemma_prefix_sum_strict_mono(nums@, j, right_int);
                                    let psj = Self::prefix_sum(nums@, j);
                                    let psr = Self::prefix_sum(nums@, right_int);
                                    let ts = Self::total_sum(nums@);
                                    assert(psj < psr);
                                    assert(ts - psj > ts - psr);
                                    assert(Self::prefix_sum(nums@, a) == ts - psj);
                                    assert(Self::prefix_sum(nums@, a) > ts - psr);
                                    assert(ts - psr == lsum_int);
                                    assert(Self::prefix_sum(nums@, a) > lsum_int);
                                    assert(a == left_int);
                                    assert(Self::prefix_sum(nums@, a) == lsum_int);
                                    assert(false);
                                }
                                assert(j == right_int);
                                assert(Self::prefix_sum(nums@, a) == lsum_int);
                                assert(lsum_int <= cur_ans);
                            }
                        }
                    };
                }
                left = left + 1;
            }
        }
        proof {
            assert forall|a: int, j: int|
                Self::valid_split(nums@, a, j)
                implies Self::prefix_sum(nums@, a) <= ans as int by {
                if a < left as int {
                } else {
                    assert(a >= left as int);
                    assert(j >= a);
                    assert(left > right);
                    assert(j > right as int);
                }
            };
            assert(Self::valid_split(nums@, ga, gj)
                && Self::prefix_sum(nums@, ga) == ans as int);
        }
        ans
    }
}

proof fn lemma_prefix_sum_step(nums: Seq<i64>, i: int)
    requires
        0 <= i < nums.len(),
    ensures
        Solution::prefix_sum(nums, i + 1)
            == Solution::prefix_sum(nums, i) + nums[i] as int,
{
}

proof fn lemma_prefix_sum_le_total(nums: Seq<i64>, i: int)
    requires
        0 <= i <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
    ensures
        Solution::prefix_sum(nums, i) <= Solution::total_sum(nums),
    decreases nums.len() - i,
{
    if i == nums.len() as int {
    } else {
        lemma_prefix_sum_step(nums, i);
        lemma_prefix_sum_le_total(nums, i + 1);
    }
}

proof fn lemma_prefix_sum_nonneg(nums: Seq<i64>)
    requires
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
    ensures
        Solution::total_sum(nums) >= 0,
{
    lemma_prefix_sum_nonneg_at(nums, nums.len() as int);
}

proof fn lemma_prefix_sum_nonneg_at(nums: Seq<i64>, end: int)
    requires
        0 <= end <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
    ensures
        Solution::prefix_sum(nums, end) >= 0,
    decreases end,
{
    if end <= 0 {
    } else {
        lemma_prefix_sum_nonneg_at(nums, end - 1);
    }
}

proof fn lemma_prefix_sum_mono(nums: Seq<i64>, a: int, b: int)
    requires
        0 <= a <= b <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
    ensures
        Solution::prefix_sum(nums, a) <= Solution::prefix_sum(nums, b),
    decreases b - a,
{
    if a == b {
    } else {
        lemma_prefix_sum_mono(nums, a, b - 1);
    }
}

proof fn lemma_prefix_sum_strict_mono(nums: Seq<i64>, a: int, b: int)
    requires
        0 <= a < b <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
    ensures
        Solution::prefix_sum(nums, a) < Solution::prefix_sum(nums, b),
    decreases b - a,
{
    if a + 1 == b {
    } else {
        lemma_prefix_sum_strict_mono(nums, a, b - 1);
    }
}

proof fn lemma_prefix_sum_strict_mono_converse(nums: Seq<i64>, a: int, b: int)
    requires
        0 <= a <= nums.len(),
        0 <= b <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] as int,
        Solution::prefix_sum(nums, a) < Solution::prefix_sum(nums, b),
    ensures
        a < b,
{
    if a >= b {
        if a == b {
        } else {
            lemma_prefix_sum_strict_mono(nums, b, a);
        }
    }
}

}
