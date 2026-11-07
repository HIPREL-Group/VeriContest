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

    proof fn lemma_max_in_range_bounded(jobs: Seq<i32>, lo: int, hi: int)
        requires
            0 <= lo <= hi,
            hi < jobs.len(),
            forall|i: int| lo <= i <= hi ==> (0 <= #[trigger] jobs[i] <= 1000),
        ensures
            0 <= Self::max_in_range(jobs, lo, hi) <= 1000,
        decreases hi - lo
    {
        if lo < hi {
            Self::lemma_max_in_range_bounded(jobs, lo, hi - 1);
        }
    }

    proof fn lemma_max_of_comm(a: int, b: int)
        ensures
            Self::max_of(a, b) == Self::max_of(b, a),
    {
    }

    proof fn lemma_max_of_swap(a: int, b: int, c: int)
        ensures
            Self::max_of(a, Self::max_of(b, c))
                == Self::max_of(b, Self::max_of(a, c)),
    {
    }

    proof fn lemma_max_in_range_lo(jobs: Seq<i32>, lo: int, hi: int)
        requires
            0 <= lo,
            lo < hi,
            hi < jobs.len(),
        ensures
            Self::max_in_range(jobs, lo, hi)
                == Self::max_of(
                    jobs[lo] as int,
                    Self::max_in_range(jobs, lo + 1, hi),
                ),
        decreases hi - lo
    {
        let a = jobs[lo] as int;
        if hi == lo + 1 {
            let b = jobs[hi] as int;
            reveal_with_fuel(Solution::max_in_range, 3);
            Self::lemma_max_of_comm(b, a);
        } else {
            Self::lemma_max_in_range_lo(jobs, lo, hi - 1);
            let x = Self::max_in_range(jobs, lo + 1, hi - 1);
            let y = jobs[hi] as int;
            assert(Self::max_in_range(jobs, lo, hi - 1) == Self::max_of(a, x));
            assert(Self::max_in_range(jobs, lo, hi) == Self::max_of(y, Self::max_of(a, x)));
            assert(Self::max_in_range(jobs, lo + 1, hi) == Self::max_of(y, x));
            Self::lemma_max_of_swap(y, a, x);
            assert(Self::max_of(y, Self::max_of(a, x)) == Self::max_of(a, Self::max_of(y, x)));
            assert(Self::max_in_range(jobs, lo, hi) == Self::max_of(a, Self::max_of(y, x)));
            assert(Self::max_of(a, Self::max_of(y, x))
                == Self::max_of(a, Self::max_in_range(jobs, lo + 1, hi)));
        }
    }

    proof fn lemma_dp_min_k_bounded(jobs: Seq<i32>, day: nat, j: int, k: int)
        requires
            day > 0,
            (day as int) - 1 <= k,
            k <= j - 1,
            day as int <= j,
            j < jobs.len(),
            forall|i: int| 0 <= i < jobs.len() ==> (0 <= #[trigger] jobs[i] <= 1000),
        ensures
            0 <= Self::dp_min_k(jobs, day, j, k) <= (day as int + 1) * 1000,
        decreases day, j - k
    {
        Self::lemma_dp_spec_bounded(jobs, (day - 1) as nat, k);
        Self::lemma_max_in_range_bounded(jobs, k + 1, j);
        if k < j - 1 {
            Self::lemma_dp_min_k_bounded(jobs, day, j, k + 1);
        }
    }

    proof fn lemma_dp_spec_bounded(jobs: Seq<i32>, day: nat, j: int)
        requires
            day as int <= j,
            j < jobs.len(),
            forall|i: int| 0 <= i < jobs.len() ==> (0 <= #[trigger] jobs[i] <= 1000),
        ensures
            0 <= Self::dp_spec(jobs, day, j) <= (day as int + 1) * 1000,
        decreases day, j + 1
    {
        if day == 0 {
            Self::lemma_max_in_range_bounded(jobs, 0, j);
        } else {
            Self::lemma_dp_min_k_bounded(jobs, day, j, (day as int) - 1);
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

        let ghost jobs = job_difficulty@;

        let mut prev_dp: Vec<i32> = Vec::new();
        prev_dp.push(job_difficulty[0]);

        let mut j: i32 = 1;
        while j < n
            invariant
                1 <= j <= n,
                1 <= n <= 300,
                1 <= d <= 10,
                d <= n,
                prev_dp@.len() == j as int,
                jobs == job_difficulty@,
                job_difficulty@.len() == n as int,
                forall|i: int|
                    0 <= i < n ==> 0 <= #[trigger] job_difficulty@[i] <= 1000,
                forall|k: int|
                    0 <= k < j ==> (#[trigger] prev_dp@[k]) as int
                        == Self::max_in_range(jobs, 0, k),
                forall|k: int| 0 <= k < j ==> 0 <= #[trigger] prev_dp@[k] <= 1000,
            decreases n - j
        {
            let prev = prev_dp[(j - 1) as usize];
            let curr = job_difficulty[j as usize];
            if prev >= curr {
                prev_dp.push(prev);
            } else {
                prev_dp.push(curr);
            }
            proof {
                assert(Self::max_in_range(jobs, 0, j as int)
                    == Self::max_of(
                        jobs[j as int] as int,
                        Self::max_in_range(jobs, 0, (j - 1) as int),
                    ));
                Self::lemma_max_in_range_bounded(jobs, 0, j as int);
            }
            j = j + 1;
        }

        let mut day: i32 = 1;
        while day < d
            invariant
                1 <= day <= d,
                1 <= n <= 300,
                1 <= d <= 10,
                d <= n,
                prev_dp@.len() == n as int,
                jobs == job_difficulty@,
                job_difficulty@.len() == n as int,
                forall|i: int|
                    0 <= i < n ==> 0 <= #[trigger] job_difficulty@[i] <= 1000,
                forall|j2: int|
                    (day - 1) as int <= j2 < n as int
                        ==> (#[trigger] prev_dp@[j2]) as int
                            == Self::dp_spec(jobs, (day - 1) as nat, j2),
                forall|j2: int|
                    (day - 1) as int <= j2 < n as int
                        ==> 0 <= #[trigger] prev_dp@[j2] <= 10000,
            decreases d - day
        {
            let mut curr_dp: Vec<i32> = Vec::new();
            let mut fill: i32 = 0;
            while fill < day
                invariant
                    0 <= fill <= day,
                    1 <= day < d,
                    curr_dp@.len() == fill as int,
                decreases day - fill
            {
                curr_dp.push(1_000_001i32);
                fill = fill + 1;
            }

            let mut j: i32 = day;
            while j < n
                invariant
                    day <= j <= n,
                    1 <= day < d,
                    1 <= n <= 300,
                    1 <= d <= 10,
                    d <= n,
                    curr_dp@.len() == j as int,
                    prev_dp@.len() == n as int,
                    jobs == job_difficulty@,
                    job_difficulty@.len() == n as int,
                    forall|i: int|
                        0 <= i < n ==> 0 <= #[trigger] job_difficulty@[i] <= 1000,
                    forall|k: int|
                        (day - 1) as int <= k < n as int
                            ==> (#[trigger] prev_dp@[k]) as int
                                == Self::dp_spec(jobs, (day - 1) as nat, k),
                    forall|k: int|
                        (day - 1) as int <= k < n as int
                            ==> 0 <= #[trigger] prev_dp@[k] <= 10000,
                    forall|k: int|
                        day as int <= k < j as int
                            ==> (#[trigger] curr_dp@[k]) as int
                                == Self::dp_spec(jobs, day as nat, k),
                    forall|k: int|
                        day as int <= k < j as int
                            ==> 0 <= #[trigger] curr_dp@[k] <= 10000,
                decreases n - j
            {
                let mut best: i32 = 1_000_001;
                let mut max_right: i32 = job_difficulty[j as usize];
                let mut k: i32 = j - 1;

                while k >= day - 1
                    invariant
                        (day - 2) as int <= k as int <= (j - 1) as int,
                        1 <= day < d,
                        day <= j < n,
                        1 <= n <= 300,
                        1 <= d <= 10,
                        d <= n,
                        prev_dp@.len() == n as int,
                        jobs == job_difficulty@,
                        job_difficulty@.len() == n as int,
                        forall|i: int|
                            0 <= i < n ==> 0 <= #[trigger] job_difficulty@[i] <= 1000,
                        forall|k2: int|
                            (day - 1) as int <= k2 < n as int
                                ==> (#[trigger] prev_dp@[k2]) as int
                                    == Self::dp_spec(jobs, (day - 1) as nat, k2),
                        forall|k2: int|
                            (day - 1) as int <= k2 < n as int
                                ==> 0 <= #[trigger] prev_dp@[k2] <= 10000,
                        max_right as int
                            == Self::max_in_range(jobs, (k + 1) as int, j as int),
                        0 <= max_right <= 1000,
                        k == j - 1 ==> best == 1_000_001i32,
                        k < j - 1 ==> best as int
                            == Self::dp_min_k(
                                jobs,
                                day as nat,
                                j as int,
                                (k + 1) as int,
                            ),
                        k < j - 1 ==> 0 <= best <= 11000,
                    decreases k - (day - 2)
                {
                    let prev_val = prev_dp[k as usize];
                    let candidate = prev_val + max_right;

                    proof {
                        Self::lemma_dp_spec_bounded(
                            jobs,
                            (day - 1) as nat,
                            k as int,
                        );
                        Self::lemma_max_in_range_bounded(
                            jobs,
                            (k + 1) as int,
                            j as int,
                        );
                    }

                    if candidate < best {
                        best = candidate;
                    }

                    proof {
                        let val_spec = Self::dp_spec(
                            jobs,
                            (day - 1) as nat,
                            k as int,
                        ) + Self::max_in_range(jobs, (k + 1) as int, j as int);
                        assert(candidate as int == val_spec);

                        if k as int == j as int - 1 {
                            assert(Self::dp_min_k(
                                jobs,
                                day as nat,
                                j as int,
                                k as int,
                            ) == val_spec);
                            assert(best as int == Self::dp_min_k(
                                jobs,
                                day as nat,
                                j as int,
                                k as int,
                            ));
                        } else {
                            assert(Self::dp_min_k(
                                jobs,
                                day as nat,
                                j as int,
                                k as int,
                            ) == Self::min_of(
                                val_spec,
                                Self::dp_min_k(
                                    jobs,
                                    day as nat,
                                    j as int,
                                    (k + 1) as int,
                                ),
                            ));
                            assert(best as int == Self::dp_min_k(
                                jobs,
                                day as nat,
                                j as int,
                                k as int,
                            ));
                        }
                    }

                    let jk = job_difficulty[k as usize];
                    if jk > max_right {
                        max_right = jk;
                    }

                    proof {
                        if (k as int) < (j as int) {
                            Self::lemma_max_in_range_lo(
                                jobs,
                                k as int,
                                j as int,
                            );
                        }
                    }

                    k = k - 1;
                }

                proof {
                    assert(best as int == Self::dp_min_k(
                        jobs,
                        day as nat,
                        j as int,
                        (day - 1) as int,
                    ));
                    assert(Self::dp_spec(jobs, day as nat, j as int)
                        == Self::dp_min_k(
                            jobs,
                            day as nat,
                            j as int,
                            (day - 1) as int,
                        ));
                    Self::lemma_dp_spec_bounded(jobs, day as nat, j as int);
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
