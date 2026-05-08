use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bit_contrib(candidates: Seq<i32>, bit: nat, idx: nat) -> nat {
        if (((candidates[idx as int] >> (bit as i32)) & 1) == 1) { 1nat } else { 0nat }
    }

    pub open spec fn count_for_bit_prefix(candidates: Seq<i32>, bit: nat, k: nat) -> nat
        decreases k,
    {
        if k == 0 {
            0
        } else {
            Self::count_for_bit_prefix(candidates, bit, (k - 1) as nat)
                + Self::bit_contrib(candidates, bit, (k - 1) as nat)
        }
    }

    pub open spec fn count_for_bit_spec(candidates: Seq<i32>, bit: nat) -> nat {
        Self::count_for_bit_prefix(candidates, bit, candidates.len() as nat)
    }

    pub open spec fn best_prefix(candidates: Seq<i32>, k: nat) -> nat
        decreases k,
    {
        if k == 0 {
            0
        } else {
            let prev = Self::best_prefix(candidates, (k - 1) as nat);
            let cur = Self::count_for_bit_spec(candidates, (k - 1) as nat);
            if cur > prev { cur } else { prev }
        }
    }

    fn count_for_bit(candidates: &Vec<i32>, bit: i32) -> (result: i32)
        requires
            1 <= candidates.len() <= 100000,
            0 <= bit < 31,
            forall |i: int| 0 <= i < candidates.len() ==> 1 <= #[trigger] candidates[i] <= 10_000_000,
        ensures
            result as nat == Self::count_for_bit_spec(candidates@, bit as nat),
            0 <= result <= candidates.len(),
    {
    }

    pub fn largest_combination(candidates: Vec<i32>) -> (result: i32)
        requires
            1 <= candidates.len() <= 100000,
            forall |i: int| 0 <= i < candidates.len() ==> 1 <= #[trigger] candidates[i] <= 10_000_000,
        ensures
            result as nat == Self::best_prefix(candidates@, 31nat),
            0 <= result <= candidates.len(),
    {
    }
}

}
