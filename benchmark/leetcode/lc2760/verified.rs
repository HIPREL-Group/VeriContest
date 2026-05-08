use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn can_extend(nums: Seq<i32>, threshold: int, k: int) -> bool
        recommends
            1 <= k < nums.len(),
    {
        nums[k] as int <= threshold && (nums[k] as int % 2) != (nums[k - 1] as int % 2)
    }

    pub open spec fn greedy_len_k(nums: Seq<i32>, threshold: int, i: int, k: int) -> int
        recommends
            0 <= i < nums.len(),
            0 <= k <= nums.len() - i - 1,
        decreases k,
    {
        if k <= 0 {
            if nums[i] as int % 2 == 0 && nums[i] as int <= threshold { 1int } else { 0int }
        } else {
            let prev = Self::greedy_len_k(nums, threshold, i, k - 1);
            let idx = i + k;
            if prev == k && Self::can_extend(nums, threshold, idx) {
                prev + 1int
            } else {
                prev
            }
        }
    }

    pub open spec fn start_len(nums: Seq<i32>, threshold: int, i: int) -> int
        recommends
            0 <= i < nums.len(),
    {
        Self::greedy_len_k(nums, threshold, i, nums.len() - i - 1)
    }

    pub open spec fn best_prefix(nums: Seq<i32>, threshold: int, upto: int) -> int
        recommends
            0 <= upto <= nums.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            let s = upto - 1;
            let prev = Self::best_prefix(nums, threshold, upto - 1);
            let cur = Self::start_len(nums, threshold, s);
            if cur > prev { cur } else { prev }
        }
    }

    pub fn longest_alternating_subarray(nums: Vec<i32>, threshold: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            1 <= threshold <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::best_prefix(nums@, threshold as int, nums.len() as int),
            0 <= result <= nums.len(),
    {
        let n = nums.len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100,
                1 <= threshold <= 100,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                0 <= i <= n,
                0 <= ans <= n,
                ans as int == Self::best_prefix(nums@, threshold as int, i as int),
            decreases n - i,
        {
            let mut len: i32 = 0;
            let mut active: bool = false;
            if nums[i] % 2 == 0 && nums[i] <= threshold {
                len = 1;
                active = true;
            }

            let mut j: usize = i + 1;
            while j < n
                invariant
                    n == nums.len(),
                    1 <= n <= 100,
                    1 <= threshold <= 100,
                    0 <= i < n,
                    i + 1 <= j <= n,
                    0 <= len <= n,
                    len as int == Self::greedy_len_k(nums@, threshold as int, i as int, j as int - (i as int + 1)),
                    active ==> len as int == j as int - i as int,
                    !active ==> (len as int) < (j as int - i as int),
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                decreases n - j,
            {
                let old_j = j;
                let old_len = len;
                let old_active = active;
                let took_extend = old_active && nums[old_j] <= threshold && nums[old_j] % 2 != nums[old_j - 1] % 2;
                let ghost old_k = old_j as int - (i as int + 1);

                if active && nums[j] <= threshold && nums[j] % 2 != nums[j - 1] % 2 {
                    len = len + 1;
                } else {
                    active = false;
                }

                proof {
                    assert(old_len as int == Self::greedy_len_k(nums@, threshold as int, i as int, old_k));
                    assert(Self::greedy_len_k(nums@, threshold as int, i as int, old_k + 1)
                        == if Self::greedy_len_k(nums@, threshold as int, i as int, old_k)
                            == old_k + 1
                            && Self::can_extend(nums@, threshold as int, old_j as int)
                        {
                            Self::greedy_len_k(nums@, threshold as int, i as int, old_k) + 1
                        } else {
                            Self::greedy_len_k(nums@, threshold as int, i as int, old_k)
                        });

                    if took_extend {
                        assert((old_len as int) == (old_j as int - i as int));
                        assert(Self::can_extend(nums@, threshold as int, old_j as int));
                        assert((len as int) == (old_len as int + 1int));
                    } else {
                        if old_active {
                            assert((old_len as int) == (old_j as int - i as int));
                            assert(!Self::can_extend(nums@, threshold as int, old_j as int));
                            assert(len == old_len);
                            assert((len as int) < (old_j as int + 1 - i as int));
                        } else {
                            assert((old_len as int) < (old_j as int - i as int));
                            assert(len == old_len);
                            assert((len as int) < (old_j as int + 1 - i as int));
                        }
                    }
                }

                j = j + 1;
            }

            proof {
                assert(j == n);
                assert(len as int == Self::greedy_len_k(nums@, threshold as int, i as int, n as int - (i as int + 1)));
                assert(len as int == Self::start_len(nums@, threshold as int, i as int));
            }

            let old_ans = ans;
            if len > ans {
                ans = len;
            }
            proof {
                assert(old_ans as int == Self::best_prefix(nums@, threshold as int, i as int));
                assert(Self::best_prefix(nums@, threshold as int, i as int + 1)
                    == if Self::start_len(nums@, threshold as int, i as int)
                        > Self::best_prefix(nums@, threshold as int, i as int)
                    {
                        Self::start_len(nums@, threshold as int, i as int)
                    } else {
                        Self::best_prefix(nums@, threshold as int, i as int)
                    });
            }

            i = i + 1;
        }

        proof {
            assert(i == n);
        }
        ans
    }
}

}
