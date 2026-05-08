use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_to(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else { Self::sum_to(s, n - 1) + s[n - 1] as int }
    }

    pub open spec fn max_to(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else {
            let prev = Self::max_to(s, n - 1);
            let cur = s[n - 1] as int;
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn spec_number_of_weeks(s: Seq<i32>) -> int {
        let total = Self::sum_to(s, s.len() as int);
        let mx = Self::max_to(s, s.len() as int);
        let rest = total - mx;
        if rest >= mx { total } else { 2 * rest + 1 }
    }

    proof fn sum_to_nonneg(s: Seq<i32>, n: int)
        requires
            0 <= n <= s.len(),
            forall |i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000,
        ensures
            Self::sum_to(s, n) >= 0,
        decreases n,
    {
        if n > 0 {
            Self::sum_to_nonneg(s, n - 1);
        }
    }

    proof fn max_to_le_sum_to(s: Seq<i32>, n: int)
        requires
            0 <= n <= s.len(),
            forall |i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000,
        ensures
            Self::max_to(s, n) <= Self::sum_to(s, n),
        decreases n,
    {
        if n > 0 {
            Self::max_to_le_sum_to(s, n - 1);
            Self::sum_to_nonneg(s, n - 1);
        }
    }

    pub fn number_of_weeks(milestones: Vec<i32>) -> (res: i64)
        requires
            1 <= milestones.len() <= 100_000,
            forall |i: int| 0 <= i < milestones.len() ==> 1 <= #[trigger] milestones[i] <= 1_000_000_000,
        ensures
            res == Self::spec_number_of_weeks(milestones@),
    {
        let n = milestones.len();
        let mut total: i64 = 0;
        let mut max_val: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == milestones.len(),
                1 <= n <= 100_000,
                0 <= i <= n,
                forall |j: int| 0 <= j < n as int ==> 1 <= #[trigger] milestones[j] <= 1_000_000_000,
                total as int == Self::sum_to(milestones@, i as int),
                max_val as int == Self::max_to(milestones@, i as int),
                0 <= total <= (i as int) * 1_000_000_000,
                0 <= max_val <= 1_000_000_000,
            decreases n - i,
        {
            let m = milestones[i] as i64;
            total = total + m;
            if m > max_val {
                max_val = m;
            }
            i += 1;
        }
        proof {
            Self::max_to_le_sum_to(milestones@, n as int);
        }
        let rest = total - max_val;
        if rest >= max_val {
            total
        } else {
            2 * rest + 1
        }
    }
}

}
