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
        let n = job_difficulty.len() as i32;
        if d > n {
            return -1i32;
        }
        let mut prev_dp: Vec<i32> = Vec::new();
        prev_dp.push(job_difficulty[0]);
        let mut j: i32 = 1;
        while j < n {
            let prev = prev_dp[(j - 1) as usize];
            let curr = job_difficulty[j as usize];
            if prev >= curr {
                prev_dp.push(prev);
            } else {
                prev_dp.push(curr);
            }
            j = j + 1;
        }
        let mut day: i32 = 1;
        while day < d {
            let mut curr_dp: Vec<i32> = Vec::new();
            let mut fill: i32 = 0;
            while fill < day {
                curr_dp.push(1_000_001i32);
                fill = fill + 1;
            }
            let mut j: i32 = day;
            while j < n {
                let mut best: i32 = 1_000_001;
                let mut max_right: i32 = job_difficulty[j as usize];
                let mut k: i32 = j - 1;
                while k >= day - 1 {
                    let prev_val = prev_dp[k as usize];
                    let candidate = prev_val + max_right;
                    if candidate < best {
                        best = candidate;
                    }
                    let jk = job_difficulty[k as usize];
                    if jk > max_right {
                        max_right = jk;
                    }
                    k = k - 1;
                }
                curr_dp.push(best);
                j = j + 1;
            }
            prev_dp = curr_dp;
            day = day + 1;
        }
        prev_dp[(n - 1) as usize]
    }
}

}
