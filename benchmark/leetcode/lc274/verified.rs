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

    proof fn lemma_subrange_full(citations: Seq<i32>)
        ensures citations.subrange(0, citations.len() as int) == citations
    {
        assert(citations =~= citations.subrange(0, citations.len() as int));
    }

    proof fn lemma_count_bounded(citations: Seq<i32>, threshold: i32)
        ensures Self::count_at_least(citations, threshold) <= citations.len()
        decreases citations.len()
    {
        if citations.len() == 0 {
        } else {
            Self::lemma_count_bounded(citations.subrange(1, citations.len() as int), threshold);
        }
    }

    proof fn lemma_count_nonnegative(citations: Seq<i32>, threshold: i32)
        ensures 
            Self::count_at_least(citations, threshold) >= 0
        decreases citations.len(), 
    {
        if citations.len() == 0 {
        } 
        else {
            Self::lemma_count_nonnegative(citations.subrange(1, citations.len() as int), threshold);
        }
    }

    proof fn lemma_count_extend(citations: Seq<i32>, j: int, threshold: i32)
        requires 
            0 <= j < citations.len()
        ensures
            Self::count_at_least(citations.subrange(0, j + 1), threshold) ==
                Self::count_at_least(citations.subrange(0, j), threshold) +
                (if citations[j] >= threshold { 1 as int } else { 0 })
        decreases j
    {
        if j == 0 {
            assert(citations.subrange(0, 0) =~= Seq::<i32>::empty());
            assert(citations.subrange(0, 1).subrange(1, 1) =~= Seq::<i32>::empty());
        } else {
            let tail = citations.subrange(1, citations.len() as int);
            
            Self::lemma_count_extend(tail, j - 1, threshold);
            
            assert(tail.subrange(0, j) =~= citations.subrange(1, j + 1));
            assert(tail.subrange(0, j - 1) =~= citations.subrange(1, j));
            assert(citations.subrange(0, j + 1).subrange(1, j + 1) =~= citations.subrange(1, j + 1));
            assert(citations.subrange(0, j).subrange(1, j) =~= citations.subrange(1, j));
        }
    }

    pub fn h_index(citations: Vec<i32>) -> (res: i32) 
        requires
            1 <= citations.len() <= 5_000, 
            forall |i: int| 0 <= i < citations.len() ==> 0 <= #[trigger] citations[i] <= 1_000,
        ensures 
            0 <= res <= citations.len(),
            Self::count_at_least(citations@, res) >= res,
            forall |h: int| res < h <= citations.len() + 1 ==> 
                #[trigger] Self::count_at_least(citations@, h as i32) < h,
    {
        let n = citations.len();

        proof {
            Self::lemma_count_bounded(citations@, (n + 1) as i32);
        }

        let mut h: usize = n;
        while h > 0 
            invariant
                n == citations.len(),
                0 <= h <= n,
                1 <= citations.len() <= 5_000, 
                forall |i: int| 0 <= i < citations.len() ==> 0 <= #[trigger] citations[i] <= 1_000,
                forall |h_cand: int| h < h_cand <= n + 1 ==> 
                    #[trigger] Self::count_at_least(citations@, h_cand as i32) < h_cand,
            decreases h, 
        {
            let mut count: usize = 0;
            let mut j: usize = 0;
            
            while j < n 
                invariant
                    n == citations.len(),
                    0 <= j <= n,
                    0 <= count <= j,
                    0 < h <= n,
                    1 <= citations.len() <= 5_000, 
                    forall |i: int| 0 <= i < citations.len() ==> 0 <= #[trigger] citations[i] <= 1_000,
                    count == Self::count_at_least(citations@.subrange(0, j as int), h as i32),
                decreases n - j, 
            {
                proof {
                    Self::lemma_count_extend(citations@, j as int, h as i32);
                }
                
                if citations[j] >= h as i32 {
                    count = count + 1;
                } 
                
                j = j + 1;
            }
            
            proof {
                Self::lemma_subrange_full(citations@);
            }
            
            if count >= h 
            {
                return h as i32;
            }
            
            h = h - 1;
        }

        proof {
            Self::lemma_count_nonnegative(citations@, 0);
        }
        
        0
    }
}

}