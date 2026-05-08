use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_index_prefix(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            0
        } else {
            let j = Self::max_index_prefix(s, n - 1);
            if s[n - 1] >= s[j] {
                n - 1
            } else {
                j
            }
        }
    }

    pub open spec fn max_value(s: Seq<i32>) -> int {
        if s.len() == 0 {
            -1
        } else {
            s[Self::max_index_prefix(s, s.len() as int)] as int
        }
    }

    pub open spec fn pick_max_mark(s: Seq<i32>) -> Seq<i32> {
        if s.len() == 0 {
            s
        } else {
            s.update(Self::max_index_prefix(s, s.len() as int), -1i32)
        }
    }

    pub open spec fn after_rounds(s: Seq<i32>, rounds: int) -> Seq<i32>
        decreases rounds,
    {
        if rounds <= 0 {
            s
        } else {
            Self::pick_max_mark(Self::after_rounds(s, rounds - 1))
        }
    }

    pub open spec fn clamp_gain(v: int, taken: int) -> int {
        if v - taken > 0 {
            v - taken
        } else {
            0
        }
    }

    pub open spec fn maximum_from_state(s: Seq<i32>, rounds: int, taken: int) -> int
        decreases rounds,
    {
        if rounds <= 0 || s.len() == 0 {
            0
        } else {
            Self::clamp_gain(Self::max_value(s), taken)
                + Self::maximum_from_state(Self::pick_max_mark(s), rounds - 1, taken + 1)
        }
    }

    pub open spec fn maximum_happiness_sum_spec(happiness: Seq<i32>, k: int) -> int {
        Self::maximum_from_state(happiness, k, 0)
    }

    pub fn maximum_happiness_sum(happiness: Vec<i32>, k: i32) -> (result: i64)
        requires
            1 <= happiness.len() <= 200000,
            1 <= k <= happiness.len(),
            forall |i: int| 0 <= i < happiness.len() ==> 1 <= #[trigger] happiness[i] <= 100000000,
        ensures
            result as int == Self::maximum_happiness_sum_spec(happiness@, k as int),
    {
        let mut a = happiness;
        let n = a.len();
        let ku = k as usize;

        let mut ans: i64 = 0;
        let mut taken: i32 = 0;
        let mut round: usize = 0;
        while round < ku {
            let mut max_idx: usize = 0;
            let mut j: usize = 1;
            while j < n {
                if a[j] >= a[max_idx] {
                    max_idx = j;
                }
                j = j + 1;
            }

            let val = a[max_idx];
            let gain = val - taken;
            if gain > 0 {
                ans = ans + gain as i64;
            }

            a.set(max_idx, -1);
            taken = taken + 1;
            round = round + 1;
        }

        ans
    }
}

}
