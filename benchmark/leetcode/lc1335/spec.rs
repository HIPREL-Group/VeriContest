use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_of(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn min_of(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    
    pub open spec fn max_in_range(jobs: Seq<i32>, lo: int, hi: int) -> int
        decreases hi - lo
    {
        if lo >= hi {
            jobs[lo] as int
        } else {
            Self::max_of(jobs[hi] as int, Self::max_in_range(jobs, lo, hi - 1))
        }
    }

    
    
    
    
    
    
    
    pub open spec fn dp_spec(jobs: Seq<i32>, day: nat, j: int) -> int
        decreases day, j + 1
    {
        if day == 0 {
            Self::max_in_range(jobs, 0, j)
        } else if j < day as int {
            1_000_001
        } else {
            Self::dp_min_k(jobs, day, j, (day as int) - 1)
        }
    }

    
    
    pub open spec fn dp_min_k(jobs: Seq<i32>, day: nat, j: int, k: int) -> int
        decreases day, j - k
    {
        if day == 0 {
            0
        } else {
            let val = Self::dp_spec(jobs, (day - 1) as nat, k)
                + Self::max_in_range(jobs, k + 1, j);
            if k >= j - 1 {
                val
            } else {
                Self::min_of(val, Self::dp_min_k(jobs, day, j, k + 1))
            }
        }
    }

    pub fn min_difficulty(job_difficulty: Vec<i32>, d: i32) -> (result: i32)
        requires
            1 <= job_difficulty.len() <= 300,
            forall|i: int|
                0 <= i < job_difficulty.len() ==> 0 <= #[trigger] job_difficulty[i] <= 1000,
            1 <= d <= 10,
        ensures
            d > job_difficulty.len() as int ==> result == -1i32,
            d <= job_difficulty.len() as int ==> result == Self::dp_spec(
                job_difficulty@,
                (d - 1) as nat,
                (job_difficulty.len() - 1) as int,
            ),
    {
    }
}

}
