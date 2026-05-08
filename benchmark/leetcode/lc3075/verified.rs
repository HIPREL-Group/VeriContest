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

    proof fn lemma_max_index_prefix_bounds(s: Seq<i32>, n: int)
        requires
            1 <= n <= s.len(),
        ensures
            0 <= Self::max_index_prefix(s, n) < n,
        decreases n,
    {
        if n <= 1 {
        } else {
            Self::lemma_max_index_prefix_bounds(s, n - 1);
        }
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
        while round < ku
            invariant
                1 <= n <= 200000,
                n == a.len(),
                1 <= k <= n as i32,
                ku == k as usize,
                0 <= round <= ku,
                taken == round as i32,
                forall |i: int| 0 <= i < n ==> -1 <= #[trigger] a[i] <= 100000000,
                a@ == Self::after_rounds(happiness@, round as int),
                ans as int + Self::maximum_from_state(a@, k as int - round as int, taken as int)
                    == Self::maximum_happiness_sum_spec(happiness@, k as int),
                0 <= ans as int <= 100000000 * round as int,
            decreases ku - round,
        {
            let ghost a_before = a@;
            let ghost round_before = round as int;
            let ghost taken_before = taken as int;
            let ghost remaining_before = k as int - round_before;
            let ghost ans_before = ans as int;

            let mut max_idx: usize = 0;
            let mut j: usize = 1;
            while j < n
                invariant
                    n == a.len(),
                    a@ == a_before,
                    1 <= j <= n,
                    0 <= max_idx < j,
                    max_idx as int == Self::max_index_prefix(a_before, j as int),
                decreases n - j,
            {
                let ghost old_idx = max_idx as int;
                proof {
                    assert(old_idx == Self::max_index_prefix(a_before, j as int));
                }
                if a[j] >= a[max_idx] {
                    max_idx = j;
                    proof {
                        assert(a_before[j as int] == a[j as int]);
                        assert(a_before[old_idx] == a[old_idx]);
                        assert(a_before[j as int] >= a_before[old_idx]);
                        assert(Self::max_index_prefix(a_before, (j + 1) as int) == j as int);
                    }
                } else {
                    proof {
                        assert(a_before[j as int] == a[j as int]);
                        assert(a_before[old_idx] == a[old_idx]);
                        assert(a_before[j as int] < a_before[old_idx]);
                        assert(Self::max_index_prefix(a_before, (j + 1) as int) == old_idx);
                    }
                }
                j = j + 1;
                proof {
                    assert(max_idx as int == Self::max_index_prefix(a_before, j as int));
                }
            }

            proof {
                assert(j == n);
                assert(max_idx as int == Self::max_index_prefix(a_before, n as int));
                Self::lemma_max_index_prefix_bounds(a_before, n as int);
                assert(round_before < k as int);
                assert(remaining_before > 0);
            }

            let val = a[max_idx];
            let gain = val - taken;
            if gain > 0 {
                ans = ans + gain as i64;
            }

            a.set(max_idx, -1);
            taken = taken + 1;
            round = round + 1;

            proof {
                assert(-1 <= val <= 100000000);
                assert(val as int == Self::max_value(a_before));
                assert(0 <= round_before <= ku as int);
                assert(ku as int == k as int);
                assert(k as int <= n as int);
                assert(round_before < ku as int);
                assert(round_before + 1 == round as int);
                if gain > 0 {
                    assert(gain as int == val as int - taken_before);
                    assert(Self::clamp_gain(val as int, taken_before) == gain as int);
                    assert(ans as int == ans_before + Self::clamp_gain(val as int, taken_before));
                    assert(0 <= taken_before);
                    assert(gain as int <= val as int);
                    assert(gain as int <= 100000000);
                    assert(ans_before <= 100000000 * round_before);
                    assert(100000000 * round_before + gain as int <= 100000000 * (round_before + 1));
                    assert(0 <= ans as int <= 100000000 * round as int);
                } else {
                    assert(gain as int == val as int - taken_before);
                    assert(Self::clamp_gain(val as int, taken_before) == 0);
                    assert(ans as int == ans_before);
                    assert(ans_before <= 100000000 * round_before);
                    assert(100000000 * round_before <= 100000000 * (round_before + 1));
                    assert(0 <= ans as int <= 100000000 * round as int);
                }

                assert(a@ == a_before.update(max_idx as int, -1i32));
                assert(a_before.update(max_idx as int, -1i32) == Self::pick_max_mark(a_before));
                assert(taken as int == taken_before + 1);
                assert(round as int == round_before + 1);
                assert(k as int - round as int == remaining_before - 1);
                assert(a@ == Self::pick_max_mark(a_before));
                assert(a@ == Self::after_rounds(happiness@, round as int));

                assert(Self::maximum_from_state(a_before, remaining_before, taken_before)
                    == Self::clamp_gain(Self::max_value(a_before), taken_before)
                        + Self::maximum_from_state(Self::pick_max_mark(a_before), remaining_before - 1, taken_before + 1));

                assert(Self::clamp_gain(Self::max_value(a_before), taken_before)
                    == Self::clamp_gain(val as int, taken_before));

                assert(Self::maximum_from_state(a@, k as int - round as int, taken as int)
                    == Self::maximum_from_state(Self::pick_max_mark(a_before), remaining_before - 1, taken_before + 1));

                assert(ans as int + Self::maximum_from_state(a@, k as int - round as int, taken as int)
                    == ans_before + Self::maximum_from_state(a_before, remaining_before, taken_before));

                assert(ans as int + Self::maximum_from_state(a@, k as int - round as int, taken as int)
                    == Self::maximum_happiness_sum_spec(happiness@, k as int));

                assert forall |i: int| 0 <= i < n implies -1 <= #[trigger] a[i] <= 100000000 by {
                    if i == max_idx as int {
                    } else {
                        assert(a[i] == a_before[i]);
                    }
                };
            }
        }

        proof {
            assert(round == ku);
            assert(k as int - round as int == 0);
            assert(Self::maximum_from_state(a@, 0, taken as int) == 0);
            assert(ans as int == Self::maximum_happiness_sum_spec(happiness@, k as int));
        }

        ans
    }
}

}
