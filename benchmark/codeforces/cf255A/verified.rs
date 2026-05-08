use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_group(seq: Seq<i64>, end: int, g: int) -> int
        recommends
            0 <= g < 3,
            0 <= end <= seq.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            let prev = end - 1;
            Self::sum_group(seq, prev, g) + (if prev % 3 == g { seq[prev] as int } else { 0 })
        }
    }

    proof fn lemma_sum_group_step(seq: Seq<i64>, k: int, g: int)
        requires
            0 <= g < 3,
            0 <= k < seq.len(),
        ensures
            Self::sum_group(seq, k + 1, g) == Self::sum_group(seq, k, g)
                + (if k % 3 == g { seq[k] as int } else { 0 }),
        decreases k,
    {
        reveal_with_fuel(Solution::sum_group, 3);
    }

    proof fn lemma_sum_group_bounds(seq: Seq<i64>, end: int, g: int)
        requires
            0 <= g < 3,
            0 <= end <= seq.len(),
            forall |j: int| 0 <= j < seq.len() ==> 1 <= #[trigger] seq[j] <= 25,
        ensures
            0 <= Self::sum_group(seq, end, g) <= 25 * end,
        decreases end,
    {
        if end <= 0 {
            reveal_with_fuel(Solution::sum_group, 1);
        } else {
            let prev = end - 1;
            Self::lemma_sum_group_bounds(seq, prev, g);
            reveal_with_fuel(Solution::sum_group, 2);
            let step = if prev % 3 == g { seq[prev] as int } else { 0 };
            assert(step <= 25);
            assert(Self::sum_group(seq, end, g) == Self::sum_group(seq, prev, g) + step);
            assert(Self::sum_group(seq, prev, g) <= 25 * prev);
            assert(25 * prev + 25 == 25 * end);
        }
    }

    pub fn workout_sums(a: Vec<i64>) -> (result: (i64, i64, i64))
        requires
            1 <= a.len() <= 20,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 25,
        ensures
            result.0 as int == Solution::sum_group(a@, a.len() as int, 0),
            result.1 as int == Solution::sum_group(a@, a.len() as int, 1),
            result.2 as int == Solution::sum_group(a@, a.len() as int, 2),
    {
        let n = a.len();
        let mut chest: i64 = 0;
        let mut biceps: i64 = 0;
        let mut back: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 20,
                n == a.len(),
                forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 25,
                0 <= i <= n,
                chest as int == Self::sum_group(a@, i as int, 0),
                biceps as int == Self::sum_group(a@, i as int, 1),
                back as int == Self::sum_group(a@, i as int, 2),
                0 <= chest <= 525,
                0 <= biceps <= 525,
                0 <= back <= 525,
            decreases n - i,
        {
            let idx = i;
            proof {
                Self::lemma_sum_group_step(a@, idx as int, 0);
                Self::lemma_sum_group_step(a@, idx as int, 1);
                Self::lemma_sum_group_step(a@, idx as int, 2);
                Self::lemma_sum_group_bounds(a@, idx as int, 0);
                Self::lemma_sum_group_bounds(a@, idx as int, 1);
                Self::lemma_sum_group_bounds(a@, idx as int, 2);
            }
            if idx % 3 == 0 {
                chest = chest + a[idx];
            } else if idx % 3 == 1 {
                biceps = biceps + a[idx];
            } else {
                back = back + a[idx];
            }
            i = idx + 1;
            proof {
                assert(chest as int == Self::sum_group(a@, i as int, 0));
                assert(biceps as int == Self::sum_group(a@, i as int, 1));
                assert(back as int == Self::sum_group(a@, i as int, 2));
            }
        }
        (chest, biceps, back)
    }
}

}
