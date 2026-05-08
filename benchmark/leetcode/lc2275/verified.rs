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
        let mut i: usize = 0;
        let mut count: i32 = 0;
        while i < candidates.len()
            invariant
                0 <= i <= candidates.len(),
                1 <= candidates.len() <= 100000,
                0 <= count <= i,
                0 <= bit < 31,
                count as nat == Self::count_for_bit_prefix(candidates@, bit as nat, i as nat),
                forall |j: int| 0 <= j < candidates.len() ==> 1 <= #[trigger] candidates[j] <= 10_000_000,
            decreases candidates.len() - i,
        {
            let old_i = i;
            let old_count = count;
            if ((candidates[i] >> bit) & 1) == 1 {
                assert(count <= i);
                assert(i < candidates.len());
                assert(candidates.len() <= 100000);
                assert(count < 2_147_483_647);
                count = count + 1;
            }
            i = i + 1;
            proof {
                assert(Self::count_for_bit_prefix(candidates@, bit as nat, i as nat)
                    == Self::count_for_bit_prefix(candidates@, bit as nat, old_i as nat)
                        + Self::bit_contrib(candidates@, bit as nat, old_i as nat));
                if ((((candidates@[old_i as int]) >> bit) & 1) == 1) {
                    assert(Self::bit_contrib(candidates@, bit as nat, old_i as nat) == 1nat);
                    assert(count == old_count + 1);
                } else {
                    assert(Self::bit_contrib(candidates@, bit as nat, old_i as nat) == 0nat);
                    assert(count == old_count);
                }
            }
        }
        count
    }

    pub fn largest_combination(candidates: Vec<i32>) -> (result: i32)
        requires
            1 <= candidates.len() <= 100000,
            forall |i: int| 0 <= i < candidates.len() ==> 1 <= #[trigger] candidates[i] <= 10_000_000,
        ensures
            result as nat == Self::best_prefix(candidates@, 31nat),
            0 <= result <= candidates.len(),
    {
        let mut bit: i32 = 0;
        let mut best: i32 = 0;
        while bit < 31
            invariant
                0 <= bit <= 31,
                1 <= candidates.len() <= 100000,
                0 <= best <= candidates.len(),
                best as nat == Self::best_prefix(candidates@, bit as nat),
                forall |i: int| 0 <= i < candidates.len() ==> 1 <= #[trigger] candidates[i] <= 10_000_000,
            decreases 31 - bit,
        {
            let old_bit = bit;
            let old_best = best;
            let cur = Self::count_for_bit(&candidates, bit);
            if cur > best {
                best = cur;
            }
            bit = bit + 1;
            proof {
                assert(Self::best_prefix(candidates@, bit as nat)
                    == {
                        let prev = Self::best_prefix(candidates@, old_bit as nat);
                        let now = Self::count_for_bit_spec(candidates@, old_bit as nat);
                        if now > prev { now } else { prev }
                    });
                if cur > old_best {
                    assert(best == cur);
                } else {
                    assert(best == old_best);
                }
            }
        }
        best
    }
}

}
