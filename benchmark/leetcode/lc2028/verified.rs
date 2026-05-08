use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::seq_sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1] as int
        }
    }

    proof fn lemma_seq_sum_push(s: Seq<i32>, x: i32)
        ensures
            Self::seq_sum(s.push(x)) == Self::seq_sum(s) + x as int,
    {
        assert(s.push(x).subrange(0, s.len() as int) =~= s);
    }

    pub fn missing_rolls(rolls: Vec<i32>, mean: i32, n: i32) -> (res: Vec<i32>)
        requires
            1 <= rolls.len() <= 100_000,
            1 <= n <= 100_000,
            1 <= mean <= 6,
            forall |i: int| 0 <= i < rolls.len() ==> 1 <= #[trigger] rolls[i] <= 6,
        ensures
            (res@ =~= Seq::<i32>::empty()) == (
                mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@) < n as int
                || mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@) > 6 * n as int
            ),
            res@ != Seq::<i32>::empty() ==> (
                res.len() == n as int
                && (forall |i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] <= 6)
                && Self::seq_sum(res@)
                    == mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@)
            ),
    {
        let mut observed_sum = 0i128;
        let mut i: usize = 0;
        while i < rolls.len()
            invariant
                1 <= rolls.len() <= 100_000,
                1 <= n <= 100_000,
                1 <= mean <= 6,
                0 <= i <= rolls.len(),
                forall |k: int| 0 <= k < rolls.len() ==> 1 <= #[trigger] rolls[k] <= 6,
                observed_sum as int == Self::seq_sum(rolls@.subrange(0, i as int)),
                0 <= observed_sum as int <= 6 * i as int,
            decreases rolls.len() - i,
        {
            let ghost prev_sum = observed_sum as int;
            observed_sum += rolls[i] as i128;
            proof {
                assert(rolls@.subrange(0, i as int + 1) =~= rolls@.subrange(0, i as int).push(rolls@[i as int]));
                Self::lemma_seq_sum_push(rolls@.subrange(0, i as int), rolls@[i as int]);
                assert(observed_sum as int == prev_sum + rolls@[i as int] as int);
                assert(observed_sum as int == Self::seq_sum(rolls@.subrange(0, i as int + 1)));
                assert(0 <= observed_sum as int <= 6 * (i as int + 1)) by (nonlinear_arith)
                    requires
                        0 <= prev_sum <= 6 * i as int,
                        1 <= rolls@[i as int] as int <= 6,
                        observed_sum as int == prev_sum + rolls@[i as int] as int,
            {}
            }
            i += 1;
        }

        proof {
            assert(rolls@.subrange(0, rolls.len() as int) =~= rolls@);
            assert(observed_sum as int == Self::seq_sum(rolls@));
            assert(rolls.len() as int + n as int <= 200_000) by (nonlinear_arith)
                requires
                    rolls.len() <= 100_000,
                    n <= 100_000,
            {}
            assert(mean as int * (rolls.len() as int + n as int) <= 1_200_000) by (nonlinear_arith)
                requires
                    1 <= mean <= 6,
                    rolls.len() as int + n as int <= 200_000,
            {}
            assert(0 <= observed_sum as int <= 600_000) by (nonlinear_arith)
                requires
                    0 <= observed_sum as int <= 6 * rolls.len() as int,
                    rolls.len() <= 100_000,
            {}
        }

        let missing_sum = mean as i128 * (rolls.len() as i128 + n as i128) - observed_sum;
        proof {
            assert(missing_sum as int == mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@));
        }
        if missing_sum < n as i128 || missing_sum > 6 * n as i128 {
            return Vec::new();
        }

        let mut result: Vec<i32> = Vec::new();
        let mut remaining_sum = missing_sum;
        let mut remaining_slots = n as i128;
        while remaining_slots > 0
            invariant
                1 <= rolls.len() <= 100_000,
                1 <= n <= 100_000,
                1 <= mean <= 6,
                forall |k: int| 0 <= k < rolls.len() ==> 1 <= #[trigger] rolls[k] <= 6,
                observed_sum as int == Self::seq_sum(rolls@),
                missing_sum as int == mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@),
                result.len() == n as int - remaining_slots as int,
                0 <= remaining_slots <= n as i128,
                forall |j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 6,
                Self::seq_sum(result@) + remaining_sum as int == missing_sum as int,
                remaining_slots as int <= remaining_sum as int <= 6 * remaining_slots as int,
            decreases remaining_slots,
        {
            let candidate = remaining_sum - 6 * (remaining_slots - 1);
            let val = if candidate > 1 { candidate } else { 1 };
            let ghost prev = result@;
            let ghost prev_remaining_sum = remaining_sum as int;
            result.push(val as i32);
            proof {
                Self::lemma_seq_sum_push(prev, val as i32);
                assert(result@ =~= prev.push(val as i32));
                if candidate > 1 {
                    assert(val == candidate);
                    assert(candidate as int <= 6) by (nonlinear_arith)
                        requires
                            candidate as int == prev_remaining_sum - 6 * (remaining_slots as int - 1),
                            prev_remaining_sum <= 6 * remaining_slots as int,
                            remaining_slots > 0,
                    {}
                    assert(1 < candidate as int) by (nonlinear_arith)
                        requires
                            candidate > 1,
                    {}
                    assert(1 <= val <= 6);
                } else {
                    assert(val == 1);
                    assert(1 <= val <= 6);
                }
                assert((val as i32) as int == val as int);
                assert forall |j: int| 0 <= j < result.len() implies 1 <= #[trigger] result[j] <= 6 by {
                    if j < prev.len() {
                        assert(result[j] == prev[j]);
                    } else {
                        assert(j == prev.len());
                    }
                };
                assert(Self::seq_sum(result@) == Self::seq_sum(prev) + val as int);
                assert(Self::seq_sum(result@) + (prev_remaining_sum - val as int) == missing_sum as int) by (nonlinear_arith)
                    requires
                        Self::seq_sum(prev) + prev_remaining_sum == missing_sum as int,
                        Self::seq_sum(result@) == Self::seq_sum(prev) + val as int,
                {}
                if candidate > 1 {
                    assert(prev_remaining_sum - val as int == 6 * (remaining_slots as int - 1)) by (nonlinear_arith)
                        requires
                            val == candidate,
                            candidate as int == prev_remaining_sum - 6 * (remaining_slots as int - 1),
                    {}
                } else {
                    assert(remaining_slots as int - 1 <= prev_remaining_sum - val as int) by (nonlinear_arith)
                        requires
                            remaining_slots as int <= prev_remaining_sum,
                            val == 1,
                    {}
                    assert(prev_remaining_sum - val as int <= 6 * (remaining_slots as int - 1)) by (nonlinear_arith)
                        requires
                            candidate as int == prev_remaining_sum - 6 * (remaining_slots as int - 1),
                            candidate <= 1,
                            val == 1,
                    {}
                }
            }
            remaining_sum -= val;
            remaining_slots -= 1;
        }

        proof {
            assert(result.len() == n as int);
            assert(remaining_slots == 0);
            assert(remaining_sum as int == 0) by (nonlinear_arith)
                requires
                    remaining_slots as int <= remaining_sum as int <= 6 * remaining_slots as int,
                    remaining_slots == 0,
            {}
            assert(Self::seq_sum(result@) == missing_sum as int) by (nonlinear_arith)
                requires
                    Self::seq_sum(result@) + remaining_sum as int == missing_sum as int,
                    remaining_sum as int == 0,
            {}
            assert(result.len() > 0);
            assert(result@ != Seq::<i32>::empty());
        }

        result
    }
}

}
