use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_zeros(s: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= s.len(),
        decreases r - l,
    {
        if l >= r {
            0
        } else {
            (if s[l] == 0 { 1int } else { 0int }) + Self::count_zeros(s, l + 1, r)
        }
    }

    proof fn lemma_count_zeros_split(s: Seq<i32>, i: int, j: int, k: int)
        requires
            0 <= i <= j <= k <= s.len(),
        ensures
            Self::count_zeros(s, i, k) == Self::count_zeros(s, i, j) + Self::count_zeros(s, j, k),
        decreases j - i,
    {
        if i < j {
            Self::lemma_count_zeros_split(s, i + 1, j, k);
        }
    }

    proof fn lemma_count_zeros_nonneg(s: Seq<i32>, i: int, j: int)
        requires
            0 <= i <= j <= s.len(),
        ensures
            Self::count_zeros(s, i, j) >= 0,
        decreases j - i,
    {
        if i < j {
            Self::lemma_count_zeros_nonneg(s, i + 1, j);
        }
    }

    proof fn lemma_count_zeros_mono_left(s: Seq<i32>, l1: int, l2: int, r: int)
        requires
            0 <= l1 <= l2 <= r <= s.len(),
        ensures
            Self::count_zeros(s, l1, r) >= Self::count_zeros(s, l2, r),
        decreases l2 - l1,
    {
        if l1 < l2 {
            Self::lemma_count_zeros_split(s, l1, l2, r);
            Self::lemma_count_zeros_nonneg(s, l1, l2);
        }
    }

    pub fn longest_subarray(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> nums[i] == 0 || nums[i] == 1,
        ensures
            0 <= result,
            (result as int) < (nums.len() as int),
            result == 0 || exists|l: int, r: int|
                0 <= l && l < r && r <= nums.len() as int
                    && r == l + result as int + 1
                    && #[trigger] Self::count_zeros(nums@, l, r) <= 1,
            forall|l: int, r: int|
                0 <= l && l < r && r <= nums.len() as int
                    && #[trigger] Self::count_zeros(nums@, l, r) <= 1 ==> r - l - 1
                    <= result as int,
    {
        let n = nums.len();
        let mut left: usize = 0;
        let mut zeros: i32 = 0;
        let mut result: i32 = 0;
        let ghost mut result_left: int = 0;
        let mut right: usize = 0;

        while right < n
            invariant
                0 <= left <= right <= n,
                n == nums.len(),
                1 <= n <= 100_000,
                forall|i: int| 0 <= i < n ==> nums@[i] == 0 || nums@[i] == 1,
                zeros == Self::count_zeros(nums@, left as int, right as int),
                zeros >= 0,
                zeros <= 1,
                0 <= result,
                (result as int) < (n as int),
                result as int >= right as int - left as int - 1,
                result == 0 || (
                    0 <= result_left && result_left + result as int + 1 <= right as int
                        && Self::count_zeros(nums@, result_left, result_left + result as int + 1)
                        <= 1
                ),
                forall|l: int, r: int|
                    0 <= l && l < r && r <= right as int
                        && #[trigger] Self::count_zeros(nums@, l, r) <= 1 ==> r - l - 1
                        <= result as int,
                left == 0 || Self::count_zeros(nums@, left as int - 1, right as int) > 1,
            decreases n - right,
        {
            proof {
                reveal_with_fuel(Solution::count_zeros, 2);
                Self::lemma_count_zeros_split(nums@, left as int, right as int, right as int + 1);
                if left > 0 {
                    Self::lemma_count_zeros_split(
                        nums@,
                        left as int - 1,
                        right as int,
                        right as int + 1,
                    );
                    Self::lemma_count_zeros_nonneg(nums@, right as int, right as int + 1);
                }
            }
            if nums[right] == 0 {
                zeros = zeros + 1;
            }
            right = right + 1;

            while zeros > 1
                invariant
                    0 <= left <= right <= n,
                    n == nums.len(),
                    1 <= n <= 100_000,
                    forall|i: int| 0 <= i < n ==> nums@[i] == 0 || nums@[i] == 1,
                    zeros == Self::count_zeros(nums@, left as int, right as int),
                    zeros >= 0,
                    0 <= result,
                    (result as int) < (n as int),
                    result == 0 || (
                        0 <= result_left && result_left + result as int + 1 < right as int
                            && Self::count_zeros(
                            nums@,
                            result_left,
                            result_left + result as int + 1,
                        ) <= 1
                    ),
                    forall|l: int, r: int|
                        0 <= l && l < r && r < right as int
                            && #[trigger] Self::count_zeros(nums@, l, r) <= 1 ==> r - l - 1
                            <= result as int,
                    left == 0 || Self::count_zeros(nums@, left as int - 1, right as int) > 1,
                decreases right - left,
            {
                proof {
                    reveal_with_fuel(Solution::count_zeros, 2);
                    Self::lemma_count_zeros_split(
                        nums@,
                        left as int,
                        left as int + 1,
                        right as int,
                    );
                }
                let ghost old_left: int = left as int;
                let ghost old_zeros: int = zeros as int;
                if nums[left] == 0 {
                    zeros = zeros - 1;
                }
                left = left + 1;
                proof {
                    assert(Self::count_zeros(nums@, old_left, right as int) == old_zeros);
                    assert(Self::count_zeros(nums@, left as int - 1, right as int) > 1);
                }
            }

            let window = if right > left {
                (right - left) as i32 - 1
            } else {
                0
            };
            proof {
                if right > left {
                    assert(window as int == right as int - left as int - 1);
                } else {
                    assert(window == 0);
                }
            }
            if window > result {
                proof {
                    result_left = left as int;
                }
                result = window;
            }

            proof {
                assert forall|l: int, r: int|
                    0 <= l && l < r && r <= right as int
                        && #[trigger] Self::count_zeros(nums@, l, r) <= 1 implies r - l - 1
                        <= result as int
                by {
                    if r < right as int {
                    } else {
                        if l >= left as int {
                            assert((left as int) < (right as int));
                            assert(r - l - 1 <= right as int - left as int - 1);
                            assert(right as int - left as int - 1 <= result as int);
                        } else {
                            if left > 0 {
                                Self::lemma_count_zeros_mono_left(
                                    nums@,
                                    l,
                                    left as int - 1,
                                    right as int,
                                );
                            }
                        }
                    }
                };
            }
        }

        result
    }
}

} 
