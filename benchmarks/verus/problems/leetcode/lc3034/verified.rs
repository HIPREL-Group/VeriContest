use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cmp(a: i32, b: i32) -> int {
        if b > a { 1 } else if b < a { -1 } else { 0 }
    }

    pub open spec fn subarray_matches(nums: Seq<i32>, pattern: Seq<i32>, start: int) -> bool {
        forall |k: int| 0 <= k < pattern.len() ==> #[trigger] pattern[k] == Self::cmp(nums[start + k], nums[start + k + 1])
    }

    pub open spec fn count_prefix(nums: Seq<i32>, pattern: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_prefix(nums, pattern, end - 1)
                + if Self::subarray_matches(nums, pattern, end - 1) { 1int } else { 0int }
        }
    }

    pub open spec fn count_matching_subarrays_spec(nums: Seq<i32>, pattern: Seq<i32>) -> int {
        Self::count_prefix(nums, pattern, nums.len() as int - pattern.len() as int)
    }

    pub fn count_matching_subarrays(nums: Vec<i32>, pattern: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            1 <= pattern.len() < nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < pattern.len() ==> -1 <= #[trigger] pattern[i] <= 1,
        ensures
            result as int == Self::count_matching_subarrays_spec(nums@, pattern@),
    {
        let n = nums.len();
        let m = pattern.len();
        let mut ans: i32 = 0;

        let mut i: usize = 0;
        while i + m < n
            invariant
                n == nums.len(),
                m == pattern.len(),
                2 <= n <= 100,
                1 <= m < n,
                0 <= i <= n - m,
                forall |t: int| 0 <= t < nums.len() ==> 1 <= #[trigger] nums[t] <= 1_000_000_000,
                forall |t: int| 0 <= t < pattern.len() ==> -1 <= #[trigger] pattern[t] <= 1,
                ans as int == Self::count_prefix(nums@, pattern@, i as int),
                0 <= ans as int <= i as int,
            decreases n - (i + m),
        {
            let ghost old_i = i as int;
            let ghost old_ans = ans as int;
            let mut ok = true;
            let mut k: usize = 0;
            while k < m
                invariant
                    n == nums.len(),
                    m == pattern.len(),
                    2 <= n <= 100,
                    1 <= m < n,
                    0 <= i <= n - m,
                    0 <= k <= m,
                    old_i == i as int,
                    old_ans == ans as int,
                    i + m < n,
                    i + k + 1 <= n,
                    forall |t: int| 0 <= t < nums.len() ==> 1 <= #[trigger] nums[t] <= 1_000_000_000,
                    forall |t: int| 0 <= t < pattern.len() ==> -1 <= #[trigger] pattern[t] <= 1,
                    ok <==> (forall |t: int| 0 <= t < k as int ==> #[trigger] pattern[t] == Self::cmp(nums[old_i + t], nums[old_i + t + 1])),
                decreases m - k,
            {
                let idx = i + k;
                proof {
                    assert(k < m);
                    assert(idx + 1 <= i + m);
                    assert(i + m < n);
                    assert(idx + 1 < n);
                }
                let d = if nums[idx + 1] > nums[idx] {
                    1
                } else if nums[idx + 1] < nums[idx] {
                    -1
                } else {
                    0
                };
                let pk = pattern[k];
                if d != pk {
                    ok = false;
                }
                proof {
                    assert(d as int == Self::cmp(nums[old_i + k as int], nums[old_i + k as int + 1]));
                    assert(pk as int == pattern[k as int] as int);
                    if d != pk {
                        assert(ok == false);
                    }
                    assert(ok <==> (forall |t: int| 0 <= t < (k + 1) as int ==> #[trigger] pattern[t] == Self::cmp(nums[old_i + t], nums[old_i + t + 1])));
                }
                k += 1;
            }
            proof {
                assert(ok <==> Self::subarray_matches(nums@, pattern@, old_i));
            }
            if ok {
                proof {
                    assert(Self::subarray_matches(nums@, pattern@, old_i));
                    assert(Self::count_prefix(nums@, pattern@, old_i + 1)
                        == Self::count_prefix(nums@, pattern@, old_i)
                            + 1);
                    assert(old_ans + 1 == Self::count_prefix(nums@, pattern@, old_i + 1));
                }
                ans += 1;
            } else {
                proof {
                    assert(!Self::subarray_matches(nums@, pattern@, old_i));
                    assert(Self::count_prefix(nums@, pattern@, old_i + 1)
                        == Self::count_prefix(nums@, pattern@, old_i)
                            + 0);
                    assert(old_ans == Self::count_prefix(nums@, pattern@, old_i + 1));
                }
            }
            i += 1;
            proof {
                assert(ans as int == Self::count_prefix(nums@, pattern@, i as int));
            }
        }

        proof {
            assert(i + m >= n);
            assert(i as int == n as int - m as int);
            assert(ans as int == Self::count_prefix(nums@, pattern@, (n - m) as int));
            assert(Self::count_matching_subarrays_spec(nums@, pattern@)
                == Self::count_prefix(nums@, pattern@, nums@.len() as int - pattern@.len() as int));
            assert(ans as int == Self::count_matching_subarrays_spec(nums@, pattern@));
            assert(ans as int <= n as int - m as int);
            assert(n as int - m as int <= 99);
            assert(ans < 2_147_483_647);
        }

        ans
    }
}

}
