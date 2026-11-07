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

        let mut h: usize = n;
        while h > 0 
        {
            let mut count: usize = 0;
            let mut j: usize = 0;
            
            while j < n 
            {
                if citations[j] >= h as i32 {
                    count = count + 1;
                } 
                
                j = j + 1;
            }

            if count >= h 
            {
                return h as i32;
            }
            
            h = h - 1;
        }

        0
    }
}

}