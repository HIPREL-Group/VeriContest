use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_at_least(citations: Seq<i32>, threshold: i32) -> int 
        decreases citations.len(),
    {
        if citations.len() == 0 {
            0
        } else {
            (if citations[0] >= threshold { 1 as int } else { 0 }) + 
            Self::count_at_least(citations.subrange(1, citations.len() as int), threshold)
        }
    }

    proof fn lemma_count_nonneg(citations: Seq<i32>, threshold: i32)
        ensures
            Self::count_at_least(citations, threshold) >= 0,
        decreases citations.len(),
    {
        if citations.len() > 0 {
            Self::lemma_count_nonneg(citations.subrange(1, citations.len() as int), threshold);
        }
    }

    proof fn lemma_count_push(seq: Seq<i32>, elem: i32, threshold: i32)
        ensures
            Self::count_at_least(seq.push(elem), threshold) == 
                Self::count_at_least(seq, threshold) + (if elem >= threshold { 1 as int } else { 0 }),
        decreases seq.len()
    {
        if seq.len() == 0 {
            let single = seq.push(elem);
            assert(single.subrange(1, 1 as int) =~= Seq::<i32>::empty());
            assert(Self::count_at_least(single.subrange(1, 1 as int), threshold) == 0);
        } else {
            Self::lemma_count_push(seq.subrange(1, seq.len() as int), elem, threshold);
            assert(seq.push(elem).subrange(1, seq.len() + 1 as int) =~= 
                seq.subrange(1, seq.len() as int).push(elem));
        }
    }

    proof fn lemma_count_from_index(citations: Seq<i32>, i: int, threshold: i32)
        requires
            forall |i: int, j: int| 0 <= i < j < citations.len() ==> 
                citations[i] < citations[j],
            0 <= i < citations.len(),
            citations[i] >= threshold,
        ensures
            Self::count_at_least(citations, threshold) >= citations.len() - i,
        decreases i
    {
        if i == 0 {
            Self::lemma_all_ge_count_full(citations, threshold);
        } else {
            Self::lemma_count_from_index(citations.subrange(1, citations.len() as int), (i - 1) as int, threshold);
        }
    }

    proof fn lemma_all_ge_count_full(citations: Seq<i32>, threshold: i32)
        requires
            forall |i: int| 0 <= i < citations.len() ==> citations[i] >= threshold,
        ensures
            Self::count_at_least(citations, threshold) == citations.len(),
        decreases citations.len()
    {
        if citations.len() > 0 {
            Self::lemma_all_ge_count_full(citations.subrange(1, citations.len() as int), threshold);
        }
    }

    proof fn lemma_count_lt_prefix(citations: Seq<i32>, k: int, threshold: i32)
        requires
            forall |i: int, j: int| 0 <= i < j < citations.len() ==> 
                citations[i] < citations[j],
            0 <= k <= citations.len(),
            forall |i: int| 0 <= i < k ==> citations[i] < threshold,
        ensures
            Self::count_at_least(citations.subrange(0, k), threshold) == 0,
        decreases k
    {
        if k == 0 {
        } else {
            Self::lemma_count_lt_prefix(citations, k - 1, threshold);
            Self::lemma_count_push(citations.subrange(0, k - 1), citations[(k - 1) as int], threshold);
            assert(citations.subrange(0, k) =~= 
                citations.subrange(0, k - 1).push(citations[(k - 1) as int]));
        }
    }

    proof fn lemma_count_bounded(citations: Seq<i32>, threshold: i32)
        ensures
            Self::count_at_least(citations, threshold) <= citations.len(),
        decreases citations.len()
    {
        if citations.len() > 0 {
            Self::lemma_count_bounded(citations.subrange(1, citations.len() as int), threshold);
        }
    }

    proof fn lemma_count_split(citations: Seq<i32>, mid: int, threshold: i32)
        requires
            0 <= mid <= citations.len(),
        ensures
            Self::count_at_least(citations, threshold)
                == Self::count_at_least(citations.subrange(0, mid), threshold)
                + Self::count_at_least(citations.subrange(mid, citations.len() as int), threshold),
        decreases citations.len()
    {
        if citations.len() == 0 {
        } else if mid == 0 {
            assert(citations.subrange(0, citations.len() as int) =~= citations);
        } else {
            let tail = citations.subrange(1, citations.len() as int);
            Self::lemma_count_split(tail, mid - 1, threshold);

            let left  = citations.subrange(0, mid);
            let right = citations.subrange(mid, citations.len() as int);
            assert(left.subrange(1, left.len() as int)
                =~= tail.subrange(0, mid - 1));
            assert(right =~= tail.subrange(mid - 1, tail.len() as int));
        }
    }

    proof fn lemma_binary_search_upper_bound(citations: Seq<i32>, i: int, num: int, h: int)
        requires
            forall |i: int, j: int| 0 <= i < j < citations.len() ==> 
                citations[i] < citations[j],
            forall |i: int| 0 <= i < citations.len() ==> 0 <= #[trigger] citations[i] <= 1_000,
            num == citations.len(),
            1 <= num <= 5_000,
            0 <= i <= num,
            forall |j: int| 0 <= j < i ==> citations[j] < (num - j),
            num - i < h <= num + 1,
            0 <= h <= 5001, 
        ensures
            Self::count_at_least(citations, h as i32) < h,
    {
        Self::lemma_count_bounded(citations, h as i32);
        
        if i == num {
            if num == 1 {
                Self::lemma_count_lt_prefix(citations, 1, h as i32);
                assert(citations.subrange(0, 1) =~= citations);
            } else {
                assert(citations[(num-2) as int] < citations[(num-1) as int]); 
            }
        } else if (h as int) > num {
        } else {
            let cutoff = num - h;
            assert forall |j: int| 0 <= j <= cutoff implies citations[j] < h as i32 by {
                if j < cutoff {
                    assert(citations[cutoff] < h as i32);  
                } 
            }
            Self::lemma_count_lt_prefix(citations, cutoff + 1, h as i32);
            Self::lemma_count_split(citations, cutoff + 1, h as i32);            
            Self::lemma_count_bounded(citations.subrange(cutoff + 1, num as int), h as i32);
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
            decreases j - i, 
        {
            let mid = (i + j) / 2;
            if citations[mid as usize] >= (num - mid) {
                j = mid;
            } else {
                i = mid + 1;
            }
        }

        proof {
            if i < num {
                Self::lemma_count_from_index(citations@, i as int, (num - i) as i32);
            } else {
                Self::lemma_count_nonneg(citations@, 0);
            }
            
            assert forall |h: int| (num - i) < h <= num + 1 implies
                #[trigger] Self::count_at_least(citations@, h as i32) < h
            by {
                Self::lemma_binary_search_upper_bound(citations@, i as int, num as int, h);
            }
        }

        num - i
    }
}

}
