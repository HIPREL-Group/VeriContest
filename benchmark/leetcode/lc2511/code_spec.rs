use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn find_next_nonzero(forts: Seq<i32>, start: nat) -> nat
        recommends start <= forts.len(),
        decreases forts.len() - start,
    {
        if start >= forts.len() {
            start
        } else if forts[start as int] != 0 {
            start
        } else {
            Self::find_next_nonzero(forts, start + 1)
        }
    }


    pub open spec fn scan_spec(forts: Seq<i32>, i: nat, best: nat) -> nat
        recommends i <= forts.len(),
        decreases forts.len() - i,
    {
        if i >= forts.len() {
            best
        } else if forts[i as int] == 1 || forts[i as int] == -1 {
            let j = Self::find_next_nonzero(forts, i + 1);
            let new_best = if j < forts.len() && forts[i as int] + forts[j as int] == 0 {
                let count = (j - i - 1) as nat;
                if best < count { count } else { best }
            } else {
                best
            };
            Self::scan_spec(forts, i + 1, new_best)
        } else {
            Self::scan_spec(forts, i + 1, best)
        }
    }

    pub open spec fn capture_forts_spec(forts: Seq<i32>) -> nat {
        Self::scan_spec(forts, 0, 0)
    }

    pub fn capture_forts(forts: Vec<i32>) -> (res: i32)
        requires
            1 <= forts.len() <= 1000,
            forall|i: int| 0 <= i < forts.len() ==>
                (forts[i] == -1 || forts[i] == 0 || forts[i] == 1),
        ensures
            0 <= res,
            res as nat == Self::capture_forts_spec(forts@),
    {
        let mut best: i32 = 0;
        let mut i: usize = 0;

        while i < forts.len()
            decreases forts.len() - i,
        {

            if forts[i] == 1 || forts[i] == -1 {
                let mut j: usize = i + 1;

                while j < forts.len() && forts[j] == 0
                    decreases forts.len() - j,
                {
                    j = j + 1;

                    
                }

                

                if j < forts.len() && forts[i] + forts[j] == 0 {
                    let count_usize = j - i - 1;

                    

                    let count = count_usize as i32;
                    if count > best {
                        best = count;
                    }

                    
                } else {
                    
                }

                
                if j > i + 1 {
                    i = j - 1;
                }
            } else {
                
            }

            i = i + 1;

            
        }

        

        best
    }
}

} 
