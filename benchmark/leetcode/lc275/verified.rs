use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_at_least(citations: Seq<i32>, threshold: i32) -> int 
        decreases citations.len()
    {
        if citations.len() == 0 {
            0
        } else {
            (if citations[0] >= threshold { 1 as int } else { 0 }) + 
            Self::count_at_least(citations.subrange(1, citations.len() as int), threshold)
        }
    }

    proof fn lemma_suffix_count(citations: Seq<i32>, start: int, threshold: i32)
        requires
            forall |i: int, j: int| 0 <= i < j < citations.len() ==> 
                citations[i] < citations[j],
            0 <= start <= citations.len(),
            forall |j: int| start <= j < citations.len() ==> citations[j] >= threshold,
        ensures
            Self::count_at_least(citations, threshold) >= citations.len() - start,
        decreases citations.len()
    {
        if citations.len() == 0 {
        } else if start == 0 {
            Self::lemma_suffix_count(citations.subrange(1, citations.len() as int), 0, threshold);
        } else {
            Self::lemma_suffix_count(citations.subrange(1, citations.len() as int), (start - 1) as int, threshold);
        }
    }

    proof fn lemma_prefix_bound(citations: Seq<i32>, cutoff: int, threshold: i32)
        requires
            forall |i: int, j: int| 0 <= i < j < citations.len() ==> 
                citations[i] < citations[j],
            0 <= cutoff <= citations.len(),
            forall |k: int| 0 <= k < cutoff ==> citations[k] < threshold,
        ensures
            Self::count_at_least(citations, threshold) <= citations.len() - cutoff,
        decreases citations.len()
    {
        if citations.len() == 0 {
        } else if cutoff == 0 {
            Self::lemma_prefix_bound(citations.subrange(1, citations.len() as int), 0, threshold);
        } else {
            Self::lemma_prefix_bound(citations.subrange(1, citations.len() as int), (cutoff - 1) as int, threshold);
        }
    }

    pub fn h_index(citations: Vec<i32>) -> (res: i32) 
        requires
            1 <= citations.len() <= 5_000, 
            forall |i: int| 0 <= i < citations.len() ==> 0 <= #[trigger] citations[i] <= 1_000,
            forall |i: int, j: int| 0 <= i < j < citations.len() ==> 
                citations[i] < citations[j], 
        ensures
            0 <= res <= citations.len(),
            Self::count_at_least(citations@, res) >= res,
            forall |h: int| res < h <= citations.len() + 1 ==> 
                #[trigger] Self::count_at_least(citations@, h as i32) < h,
    {
        let num = citations.len() as i32;
        let mut i: i32 = 0;
        let mut j: i32 = num;

        proof {
            Self::lemma_suffix_count(citations@, 0, 0);
            assert forall |h: int| num < h <= num + 1 implies
                #[trigger] Self::count_at_least(citations@, h as i32) < h
            by {
                Self::lemma_prefix_bound(citations@, 0, h as i32);
            }
        }

        while i < j 
            invariant
                num == citations.len(),
                1 <= citations.len() <= 5_000, 
                forall |k: int| 0 <= k < citations.len() ==> 0 <= #[trigger] citations[k] <= 1_000,
                forall |k: int, l: int| 0 <= k < l < citations.len() ==> 
                    citations[k] < citations[l],
                0 <= i <= j <= num,
                forall |k: int| 0 <= k < i ==> citations[k] < (num - k),
                forall |k: int| j <= k < num ==> citations[k] >= (num - k),
                Self::count_at_least(citations@, (num - j) as i32) >= num - j,
                forall |h: int| num - i < h <= num + 1 ==> 
                    #[trigger] Self::count_at_least(citations@, h as i32) < h,
            decreases j - i, 
        {
            let mid = (i + j) / 2;

            if citations[mid as usize] >= (num - mid) {
                proof {
                    Self::lemma_suffix_count(citations@, mid as int, (num - mid) as i32);
                }
                j = mid;
            } else {
                proof {
                    assert forall |h: int| num - (mid + 1) < h <= num + 1 implies
                        #[trigger] Self::count_at_least(citations@, h as i32) < h
                    by {
                        Self::lemma_prefix_bound(citations@, mid + 1, h as i32);
                    }
                }
                i = mid + 1;
            }
        }

        num - i
    }
}

}
