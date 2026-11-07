use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inner_count(hours: Seq<i32>, i: int, j: int) -> int
        decreases hours.len() - j,
    {
        if j >= hours.len() {
            0
        } else {
            (if (hours[i] as int + hours[j] as int) % 24 == 0 { 1int } else { 0int })
                + Self::inner_count(hours, i, j + 1)
        }
    }

    pub open spec fn pair_count(hours: Seq<i32>, i: int) -> int
        decreases hours.len() - i,
    {
        if i >= hours.len() {
            0
        } else {
            Self::inner_count(hours, i, i + 1) + Self::pair_count(hours, i + 1)
        }
    }

    proof fn lemma_inner_count_bound(hours: Seq<i32>, i: int, j: int)
        requires
            0 <= i < hours.len(),
            0 <= j <= hours.len(),
        ensures
            0 <= Self::inner_count(hours, i, j) <= hours.len() - j,
        decreases hours.len() - j,
    {
        if j < hours.len() {
            Self::lemma_inner_count_bound(hours, i, j + 1);
        }
    }

    proof fn lemma_pair_count_bound(hours: Seq<i32>, i: int)
        requires
            0 <= i <= hours.len(),
        ensures
            0 <= Self::pair_count(hours, i) <= (hours.len() - i) * hours.len(),
        decreases hours.len() - i,
    {
        if i < hours.len() {
            Self::lemma_inner_count_bound(hours, i, i + 1);
            Self::lemma_pair_count_bound(hours, i + 1);
            assert((hours.len() - i) * hours.len() == hours.len() + (hours.len() - i - 1) * hours.len()) by (nonlinear_arith)
                requires i < hours.len() {}
        }
    }

    pub fn count_complete_day_pairs(hours: Vec<i32>) -> (res: i32)
        requires
            1 <= hours.len() <= 100,
            forall|i: int| 0 <= i < hours.len() ==> 1 <= #[trigger] hours[i] <= 1_000_000_000,
        ensures
            res as int == Self::pair_count(hours@, 0),
            0 <= res <= hours.len() * hours.len(),
    {
        let mut count: i32 = 0;
        let n = hours.len();

        proof {
            Self::lemma_pair_count_bound(hours@, 0);
            assert(hours.len() as int * hours.len() as int <= 10000) by (nonlinear_arith)
                requires 1 <= hours.len() <= 100 {}
        }

        for i in 0..n
            invariant
                n == hours.len(),
                1 <= n <= 100,
                forall|ii: int| 0 <= ii < hours.len() ==> 1 <= #[trigger] hours[ii] <= 1_000_000_000,
                count as int == Self::pair_count(hours@, 0)
                    - Self::pair_count(hours@, i as int),
                0 <= count <= 10000,
                Self::pair_count(hours@, 0) <= 10000,
        {
            let mut inner: i32 = 0;
            for j in (i + 1)..n
                invariant
                    n == hours.len(),
                    1 <= n <= 100,
                    0 <= i < n,
                    i < j,
                    forall|ii: int| 0 <= ii < hours.len() ==> 1 <= #[trigger] hours[ii] <= 1_000_000_000,
                    inner as int == Self::inner_count(hours@, i as int, i as int + 1)
                        - Self::inner_count(hours@, i as int, j as int),
                    0 <= inner <= j - i - 1,
            {
                proof {
                    Self::lemma_inner_count_bound(hours@, i as int, j as int + 1);
                    assert(hours@[i as int] as int + hours@[j as int] as int <= 2_000_000_000) by (nonlinear_arith)
                        requires 1 <= hours@[i as int] <= 1_000_000_000, 1 <= hours@[j as int] <= 1_000_000_000 {}
                }
                if (hours[i] as u32 + hours[j] as u32) % 24 == 0 {
                    inner += 1;
                }
            }

            proof {
                Self::lemma_inner_count_bound(hours@, i as int, i as int + 1);
                Self::lemma_pair_count_bound(hours@, i as int + 1);
            }

            count += inner;
        }
        count
    }
}

}
