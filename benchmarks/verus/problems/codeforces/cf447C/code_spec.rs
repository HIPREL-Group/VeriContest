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
            return 1;
        }
        let mut pre: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            pre.push(1i32);
            j = j + 1;
        }
        j = 1;
        while j < n {
            if nums[j] > nums[j - 1] {
                pre.set(j, pre[j - 1] + 1);
            }
            j = j + 1;
        }
        let mut suf: Vec<i32> = Vec::new();
        j = 0;
        while j < n {
            suf.push(1i32);
            j = j + 1;
        }
        j = n - 1;
        while j > 0 {
            j = j - 1;
            if nums[j] < nums[j + 1] {
                suf.set(j, suf[j + 1] + 1);
            }
        }
        let mut ans: i32 = 1;
        j = 0;
        while j < n {
            if pre[j] > ans {
                ans = pre[j];
            }
            j = j + 1;
        }
        j = 0;
        while j < n {
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
            j = j + 1;
        }
        ans as i64
    }
}

}
