use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_inc_len(s: Seq<i64>, j: int) -> int
    decreases j,
{
    if j <= 0 { 1 }
    else if s[j] > s[j - 1] { prefix_inc_len(s, j - 1) + 1 }
    else { 1 }
}

pub open spec fn suffix_inc_len(s: Seq<i64>, j: int, n: int) -> int
    decreases n - j,
{
    if j + 1 >= n { 1 }
    else if s[j] < s[j + 1] { suffix_inc_len(s, j + 1, n) + 1 }
    else { 1 }
}

pub open spec fn candidate_at(s: Seq<i64>, j: int, n: int) -> int {
    let left = if j == 0 { 0int } else { prefix_inc_len(s, j - 1) };
    let right = if j + 1 >= n { 0int } else { suffix_inc_len(s, j + 1, n) };
    let alo = if j == 0 { -2_000_000_000int } else { s[j - 1] as int };
    let ahi = if j + 1 >= n { 2_000_000_000int } else { s[j + 1] as int };
    if alo + 1 < ahi {
        left + 1 + right
    } else {
        let m = if left > right { left } else { right };
        m + 1
    }
}

pub open spec fn max_pre_upto(s: Seq<i64>, j: int) -> int
    decreases j + 1,
{
    if j < 0 { 1 }
    else {
        let cur = prefix_inc_len(s, j);
        let prev = max_pre_upto(s, j - 1);
        if cur > prev { cur } else { prev }
    }
}

pub open spec fn max_cand_upto(s: Seq<i64>, n: int, j: int, base: int) -> int
    decreases j + 1,
{
    if j < 0 { base }
    else {
        let cur = candidate_at(s, j, n);
        let prev = max_cand_upto(s, n, j - 1, base);
        if cur > prev { cur } else { prev }
    }
}

pub open spec fn answer_spec(s: Seq<i64>) -> int {
    let n = s.len() as int;
    if n <= 0 { 0 }
    else { max_cand_upto(s, n, n - 1, max_pre_upto(s, n - 1)) }
}

proof fn lemma_prefix_inc_len_bounds(s: Seq<i64>, j: int)
    requires 0 <= j < s.len(),
    ensures 1 <= prefix_inc_len(s, j) <= j + 1,
    decreases j,
{
    if j > 0 && s[j] > s[j - 1] {
        lemma_prefix_inc_len_bounds(s, j - 1);
    }
}

proof fn lemma_suffix_inc_len_bounds(s: Seq<i64>, j: int, n: int)
    requires 0 <= j < n, n == s.len() as int,
    ensures 1 <= suffix_inc_len(s, j, n) <= n - j,
    decreases n - j,
{
    if j + 1 < n && s[j] < s[j + 1] {
        lemma_suffix_inc_len_bounds(s, j + 1, n);
    }
}

proof fn lemma_candidate_bounds(s: Seq<i64>, j: int, n: int)
    requires
        0 <= j < n,
        n == s.len() as int,
        n >= 1,
        forall |k: int| #![trigger s[k]] 0 <= k < n ==> 1 <= s[k] <= 1_000_000_000,
    ensures
        1 <= candidate_at(s, j, n) <= n,
{
    if j > 0 {
        lemma_prefix_inc_len_bounds(s, j - 1);
    }
    if j + 1 < n {
        lemma_suffix_inc_len_bounds(s, j + 1, n);
    }
}

proof fn lemma_max_pre_bounds(s: Seq<i64>, j: int, n: int)
    requires -1 <= j < n, n == s.len() as int, n >= 1,
    ensures 1 <= max_pre_upto(s, j) <= n,
    decreases j + 1,
{
    if j >= 0 {
        lemma_prefix_inc_len_bounds(s, j);
        lemma_max_pre_bounds(s, j - 1, n);
    }
}

proof fn lemma_max_cand_bounds(s: Seq<i64>, n: int, j: int, base: int)
    requires
        -1 <= j < n,
        n == s.len() as int,
        n >= 1,
        1 <= base <= n,
        forall |k: int| #![trigger s[k]] 0 <= k < n ==> 1 <= s[k] <= 1_000_000_000,
    ensures
        1 <= max_cand_upto(s, n, j, base) <= n,
    decreases j + 1,
{
    if j >= 0 {
        lemma_candidate_bounds(s, j, n);
        lemma_max_cand_bounds(s, n, j - 1, base);
    }
}

impl Solution {
    pub fn longest_subsegment_one_change_strict_inc(nums: Vec<i64>) -> (result: i64)
        requires
            1 <= nums.len() <= 100_000,
            forall |k: int|
                #![trigger nums[k]]
                0 <= k < nums.len() ==> 1 <= nums[k] <= 1_000_000_000,
        ensures
            1 <= result <= nums.len() as i64,
            result as int == answer_spec(nums@),
    {
        let n: usize = nums.len();
        if n == 1 {
            proof {
                assert(prefix_inc_len(nums@, 0) == 1);
                assert(max_pre_upto(nums@, -1) == 1);
                assert(max_pre_upto(nums@, 0) == 1);
                assert(candidate_at(nums@, 0, 1) == 1);
                assert(max_cand_upto(nums@, 1, -1, 1) == 1);
                assert(max_cand_upto(nums@, 1, 0, 1) == 1);
                assert(answer_spec(nums@) == 1);
            }
            return 1;
        }
        let mut pre: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                n == nums.len(),
                n <= 100_000,
                j <= n,
                pre.len() == j,
                forall |k: int| 0 <= k < j as int ==> #[trigger] pre[k] == 1i32,
            decreases n - j,
        {
            pre.push(1i32);
            j = j + 1;
        }
        j = 1;
        while j < n
            invariant
                n == nums.len(),
                n >= 2,
                n <= 100_000,
                pre.len() == n,
                1 <= j <= n,
                forall |k: int| 0 <= k < j as int ==> #[trigger] pre[k] as int == prefix_inc_len(nums@, k),
                forall |k: int| j as int <= k < n as int ==> #[trigger] pre[k] == 1i32,
                forall |k: int| 0 <= k < j as int ==> 1 <= #[trigger] pre[k] as int <= k + 1,
            decreases n - j,
        {
            if nums[j] > nums[j - 1] {
                proof {
                    lemma_prefix_inc_len_bounds(nums@, j as int - 1);
                    assert(pre[j as int - 1] as int == prefix_inc_len(nums@, j as int - 1));
                    assert(pre[j as int - 1] as int <= j as int);
                    assert(prefix_inc_len(nums@, j as int) == prefix_inc_len(nums@, j as int - 1) + 1);
                }
                pre.set(j, pre[j - 1] + 1);
                proof {
                    lemma_prefix_inc_len_bounds(nums@, j as int);
                    assert forall |k: int| 0 <= k < j as int + 1 implies #[trigger] pre[k] as int == prefix_inc_len(nums@, k) by {
                    }
                    assert forall |k: int| j as int + 1 <= k < n as int implies #[trigger] pre[k] == 1i32 by {
                    }
                    assert forall |k: int| 0 <= k < j as int + 1 implies 1 <= #[trigger] pre[k] as int <= k + 1 by {
                        if k < j as int {
                        } else {
                            lemma_prefix_inc_len_bounds(nums@, k);
                        }
                    }
                }
            } else {
                proof {
                    assert(prefix_inc_len(nums@, j as int) == 1);
                    assert(pre[j as int] == 1i32);
                    assert forall |k: int| 0 <= k < j as int + 1 implies #[trigger] pre[k] as int == prefix_inc_len(nums@, k) by {
                    }
                    assert forall |k: int| 0 <= k < j as int + 1 implies 1 <= #[trigger] pre[k] as int <= k + 1 by {
                        if k < j as int {
                        } else {
                            assert(pre[k] == 1i32);
                        }
                    }
                }
            }
            j = j + 1;
        }
        let mut suf: Vec<i32> = Vec::new();
        j = 0;
        while j < n
            invariant
                n == nums.len(),
                n <= 100_000,
                j <= n,
                suf.len() == j,
                forall |k: int| 0 <= k < j as int ==> #[trigger] suf[k] == 1i32,
            decreases n - j,
        {
            suf.push(1i32);
            j = j + 1;
        }
        j = n - 1;
        proof {
            assert(suffix_inc_len(nums@, n as int - 1, n as int) == 1);
        }
        while j > 0
            invariant
                n == nums.len(),
                n >= 2,
                n <= 100_000,
                suf.len() == n,
                j < n,
                forall |k: int| j as int <= k < n as int ==> #[trigger] suf[k] as int == suffix_inc_len(nums@, k, n as int),
                forall |k: int| j as int <= k < n as int ==> 1 <= #[trigger] suf[k] as int <= n as int - k,
                forall |k: int| 0 <= k < j as int ==> #[trigger] suf[k] == 1i32,
            decreases j,
        {
            j = j - 1;
            if nums[j] < nums[j + 1] {
                proof {
                    lemma_suffix_inc_len_bounds(nums@, j as int + 1, n as int);
                    assert(suf[j as int + 1] as int == suffix_inc_len(nums@, j as int + 1, n as int));
                    assert(suf[j as int + 1] as int <= n as int - j as int - 1);
                    assert(suffix_inc_len(nums@, j as int, n as int) == suffix_inc_len(nums@, j as int + 1, n as int) + 1);
                }
                suf.set(j, suf[j + 1] + 1);
                proof {
                    lemma_suffix_inc_len_bounds(nums@, j as int, n as int);
                    assert forall |k: int| j as int <= k < n as int implies #[trigger] suf[k] as int == suffix_inc_len(nums@, k, n as int) by {
                    }
                    assert forall |k: int| j as int <= k < n as int implies 1 <= #[trigger] suf[k] as int <= n as int - k by {
                        if k == j as int {
                            lemma_suffix_inc_len_bounds(nums@, k, n as int);
                        }
                    }
                    assert forall |k: int| 0 <= k < j as int implies #[trigger] suf[k] == 1i32 by {
                    }
                }
            } else {
                proof {
                    assert(suffix_inc_len(nums@, j as int, n as int) == 1);
                    assert(suf[j as int] == 1i32);
                    assert forall |k: int| j as int <= k < n as int implies #[trigger] suf[k] as int == suffix_inc_len(nums@, k, n as int) by {
                    }
                    assert forall |k: int| j as int <= k < n as int implies 1 <= #[trigger] suf[k] as int <= n as int - k by {
                        if k == j as int {
                            assert(suf[k] == 1i32);
                        }
                    }
                }
            }
        }
        let mut ans: i32 = 1;
        j = 0;
        while j < n
            invariant
                n == nums.len(),
                n >= 2,
                n <= 100_000,
                pre.len() == n,
                suf.len() == n,
                j <= n,
                forall |k: int| 0 <= k < n as int ==> #[trigger] pre[k] as int == prefix_inc_len(nums@, k),
                forall |k: int| 0 <= k < n as int ==> #[trigger] suf[k] as int == suffix_inc_len(nums@, k, n as int),
                ans as int == max_pre_upto(nums@, j as int - 1),
                1 <= ans as int <= n as int,
            decreases n - j,
        {
            proof {
                lemma_prefix_inc_len_bounds(nums@, j as int);
            }
            if pre[j] > ans {
                ans = pre[j];
            }
            proof {
                assert(ans as int == max_pre_upto(nums@, j as int));
                lemma_max_pre_bounds(nums@, j as int, n as int);
            }
            j = j + 1;
        }
        let ghost ghost_base: int = ans as int;
        proof {
            lemma_max_pre_bounds(nums@, n as int - 1, n as int);
        }
        j = 0;
        while j < n
            invariant
                n == nums.len(),
                n >= 2,
                n <= 100_000,
                pre.len() == n,
                suf.len() == n,
                j <= n,
                forall |k: int| 0 <= k < n as int ==> #[trigger] pre[k] as int == prefix_inc_len(nums@, k),
                forall |k: int| 0 <= k < n as int ==> #[trigger] suf[k] as int == suffix_inc_len(nums@, k, n as int),
                forall |k: int| 0 <= k < n as int ==> 1 <= (#[trigger] pre[k]) as int <= k + 1,
                forall |k: int| 0 <= k < n as int ==> 1 <= (#[trigger] suf[k]) as int <= n as int - k,
                forall |k: int|
                    #![trigger nums[k]]
                    0 <= k < nums.len() ==> 1 <= nums[k] <= 1_000_000_000,
                ghost_base == max_pre_upto(nums@, n as int - 1),
                1 <= ghost_base <= n as int,
                ans as int == max_cand_upto(nums@, n as int, j as int - 1, ghost_base),
                1 <= ans as int <= n as int,
            decreases n - j,
        {
            let left: i32 = if j == 0 {
                0
            } else {
                pre[j - 1]
            };
            let right: i32 = if j + 1 >= n {
                0
            } else {
                suf[j + 1]
            };
            let alo: i64 = if j == 0 {
                -2_000_000_000
            } else {
                nums[j - 1]
            };
            let ahi: i64 = if j + 1 >= n {
                2_000_000_000
            } else {
                nums[j + 1]
            };
            proof {
                lemma_candidate_bounds(nums@, j as int, n as int);
                assert(0 <= left as int <= j as int);
                assert(0 <= right as int <= n as int - j as int - 1);
                assert(left as int + 1 + right as int <= n as int);
            }
            let cand: i32 = if alo + 1 < ahi {
                left + 1 + right
            } else {
                let m: i32 = if left > right {
                    left
                } else {
                    right
                };
                m + 1
            };
            if cand > ans {
                ans = cand;
            }
            proof {
                assert(cand as int == candidate_at(nums@, j as int, n as int));
                assert(ans as int == max_cand_upto(nums@, n as int, j as int, ghost_base));
                lemma_max_cand_bounds(nums@, n as int, j as int, ghost_base);
            }
            j = j + 1;
        }
        proof {
            assert(ans as int == max_cand_upto(nums@, n as int, n as int - 1, ghost_base));
            assert(ghost_base == max_pre_upto(nums@, n as int - 1));
            assert(ans as int == answer_spec(nums@));
        }
        ans as i64
    }
}

}
