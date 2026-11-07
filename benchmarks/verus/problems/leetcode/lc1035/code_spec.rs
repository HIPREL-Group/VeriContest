use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_strictly_sorted(s: Seq<int>) -> bool {
    forall |k: int, l: int| 0 <= k < l < s.len() ==> s[k] < s[l]
}

pub open spec fn all_in_range(s: Seq<int>, hi: int) -> bool {
    forall |k: int| 0 <= k < s.len() ==> 0 <= #[trigger] s[k] < hi
}

pub open spec fn is_common_subseq(a: Seq<i32>, b: Seq<i32>, ia: Seq<int>, ib: Seq<int>) -> bool {
    ia.len() == ib.len()
    && is_strictly_sorted(ia)
    && is_strictly_sorted(ib)
    && all_in_range(ia, a.len() as int)
    && all_in_range(ib, b.len() as int)
    && (forall |k: int| 0 <= k < ia.len() ==> a[#[trigger] ia[k]] == b[#[trigger] ib[k]])
}

pub open spec fn lcs(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int) -> int
    decreases i, j
{
    if i <= 0 || j <= 0 {
        0
    } else if s1[i - 1] == s2[j - 1] {
        lcs(s1, s2, i - 1, j - 1) + 1
    } else {
        let a = lcs(s1, s2, i - 1, j);
        let b = lcs(s1, s2, i, j - 1);
        if a >= b { a } else { b }
    }
}

impl Solution {
    pub fn max_uncrossed_lines(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 500,
            1 <= nums2.len() <= 500,
            forall |i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 2000,
            forall |i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 2000,
        ensures
            exists |ia: Seq<int>, ib: Seq<int>| #[trigger] is_common_subseq(nums1@, nums2@, ia, ib) && ia.len() == result as int,
            forall |ia: Seq<int>, ib: Seq<int>| #[trigger] is_common_subseq(nums1@, nums2@, ia, ib) ==> ia.len() <= result as int,
    {
        let m = nums1.len();
        let n = nums2.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            dp.push(0);
            k = k + 1;
        }
        let mut i: usize = 1;
        while i <= m {
            let mut prev: i32 = 0;
            let mut j: usize = 1;
            while j <= n {
                let curr = dp[j];
                if nums1[i - 1] == nums2[j - 1] {
                    dp.set(j, prev + 1);
                } else {
                    let a = curr;
                    let b = dp[j - 1];
                    if a >= b {
                        dp.set(j, a);
                    } else {
                        dp.set(j, b);
                    }
                }
                prev = curr;
                j = j + 1;
            }
            i = i + 1;
        }
        dp[n]
    }
}

}
