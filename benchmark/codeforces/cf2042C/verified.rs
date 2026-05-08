use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn weight(owners: Seq<i64>, i: int) -> int {
        if owners[i] == 1 { 1 } else { -1 }
    }

    pub open spec fn suffix_gain(owners: Seq<i64>, start: int) -> int
        decreases if start >= owners.len() { 0 } else { owners.len() - start },
    {
        if start >= owners.len() {
            0
        } else {
            Self::weight(owners, start) + Self::suffix_gain(owners, start + 1)
        }
    }

    pub open spec fn gain_count_from(owners: Seq<i64>, gain: int, start: int) -> int
        decreases if start >= owners.len() { 0 } else { owners.len() - start },
    {
        if start >= owners.len() {
            0
        } else {
            Self::gain_count_from(owners, gain, start + 1)
                + if 1 <= start && Self::suffix_gain(owners, start) == gain { 1int } else { 0int }
        }
    }

    pub open spec fn ceil_div_pos(num: int, den: int) -> int {
        if num <= 0 { 0 } else { (num + den - 1) / den }
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn greedy_answer_rec(owners: Seq<i64>, k: int, gain: int, total: int, cuts: int) -> int
        decreases if gain <= 0 { 0 } else { gain },
    {
        if total >= k {
            cuts + 1
        } else if gain <= 0 {
            -1
        } else {
            let cnt = Self::gain_count_from(owners, gain, 1);
            let need = Self::ceil_div_pos(k - total, gain);
            let take = Self::min_int(cnt, need);
            Self::greedy_answer_rec(owners, k, gain - 1, total + take * gain, cuts + take)
        }
    }

    pub open spec fn greedy_answer(owners: Seq<i64>, k: int) -> int {
        Self::greedy_answer_rec(owners, k, owners.len() as int, 0, 0)
    }

    proof fn lemma_suffix_bounds(owners: Seq<i64>, start: int)
        requires
            forall|i: int| 0 <= i < owners.len() ==> #[trigger] owners[i] == 0 || #[trigger] owners[i] == 1,
            0 <= start <= owners.len(),
        ensures
            -(owners.len() - start) <= Self::suffix_gain(owners, start) <= owners.len() - start,
        decreases if start >= owners.len() { 0 } else { owners.len() - start },
    {
        if start < owners.len() {
            Self::lemma_suffix_bounds(owners, start + 1);
        }
    }

    proof fn lemma_gain_count_bounds(owners: Seq<i64>, gain: int, start: int)
        requires
            0 <= start <= owners.len(),
        ensures
            0 <= Self::gain_count_from(owners, gain, start) <= owners.len() - start,
        decreases if start >= owners.len() { 0 } else { owners.len() - start },
    {
        if start < owners.len() {
            Self::lemma_gain_count_bounds(owners, gain, start + 1);
        }
    }

    fn zero_vec(size: usize) -> (res: Vec<i64>)
        ensures
            res.len() == size,
            forall|i: int| 0 <= i < size ==> #[trigger] res@[i] == 0,
    {
        let mut res: Vec<i64> = Vec::new();
        let mut fill: usize = 0;
        while fill < size
            invariant
                res.len() == fill,
                fill <= size,
                forall|i: int| 0 <= i < fill ==> #[trigger] res@[i] == 0,
            decreases size - fill,
        {
            res.push(0);
            fill = fill + 1;
        }
        res
    }

    fn build_gain_counts(owners: &Vec<i64>) -> (counts: Vec<i64>)
        requires
            2 <= owners.len() <= 200000,
            forall|i: int| 0 <= i < owners.len() ==> #[trigger] owners@[i] == 0 || #[trigger] owners@[i] == 1,
        ensures
            counts.len() == owners.len() + 1,
            forall|g: int| 1 <= g < counts.len() ==> #[trigger] counts@[g] as int == Self::gain_count_from(owners@, g, 1),
    {
        let n = owners.len();
        let mut counts: Vec<i64> = Solution::zero_vec(n + 1);
        let mut suffix: i64 = 0;
        let mut i: usize = n;
        while i > 1
            invariant
                counts.len() == n + 1,
                2 <= n <= 200000,
                n == owners@.len(),
                1 <= i <= n,
                forall|j: int| 0 <= j < owners@.len() ==> #[trigger] owners@[j] == 0 || #[trigger] owners@[j] == 1,
                suffix as int == Self::suffix_gain(owners@, i as int),
                -(n as int - i as int) <= suffix as int <= n as int - i as int,
                forall|g: int| 1 <= g < counts.len() ==> #[trigger] counts@[g] as int == Self::gain_count_from(owners@, g, i as int),
            decreases i - 1,
        {
            let i0 = i - 1;
            proof {
                assert(0 <= i0 as int && (i0 as int) < owners@.len());
                assert(owners@[i0 as int] == 0 || owners@[i0 as int] == 1);
                Self::lemma_suffix_bounds(owners@, i0 as int);
            }
            let ghost old_counts = counts@;
            let old_suffix = suffix;
            if owners[i0] == 1 {
                suffix = suffix + 1;
            } else {
                suffix = suffix - 1;
            }
            if suffix > 0 {
                proof {
                    assert(1 <= suffix as int <= n as int) by(nonlinear_arith)
                        requires
                            1 <= i0 < n,
                            -(n as int - i0 as int) <= suffix as int <= n as int - i0 as int,
                            suffix > 0;
                    Self::lemma_gain_count_bounds(owners@, suffix as int, i as int);
                    assert(0 <= counts@[suffix as int] as int <= n as int - i as int);
                }
                counts.set(suffix as usize, counts[suffix as usize] + 1);
            }
            i = i0;
            proof {
                if owners@[i as int] == 1 {
                    assert(Self::weight(owners@, i as int) == 1);
                    assert(suffix as int == old_suffix as int + 1);
                } else {
                    assert(Self::weight(owners@, i as int) == -1);
                    assert(suffix as int == old_suffix as int - 1);
                }
                assert(Self::suffix_gain(owners@, i as int) == Self::weight(owners@, i as int) + Self::suffix_gain(owners@, i as int + 1));
                assert(suffix as int == Self::suffix_gain(owners@, i as int));
                assert forall|g: int| 1 <= g < counts.len() implies #[trigger] counts@[g] as int == Self::gain_count_from(owners@, g, i as int) by {
                    if suffix > 0 && g == suffix as int {
                        assert(old_counts[g] as int == Self::gain_count_from(owners@, g, i as int + 1));
                        assert(counts@[g] as int == old_counts[g] as int + 1);
                        assert(1 <= i as int);
                        assert(Self::suffix_gain(owners@, i as int) == g);
                        assert(Self::gain_count_from(owners@, g, i as int)
                            == Self::gain_count_from(owners@, g, i as int + 1) + 1int);
                    } else {
                        assert(old_counts[g] as int == Self::gain_count_from(owners@, g, i as int + 1));
                        if suffix <= 0 {
                            assert(suffix as int == Self::suffix_gain(owners@, i as int));
                            assert(g >= 1);
                            assert(suffix as int <= 0);
                            assert(Self::suffix_gain(owners@, i as int) != g);
                        } else {
                            assert(g != suffix as int);
                            assert(Self::suffix_gain(owners@, i as int) != g);
                        }
                        assert((if 1 <= i as int && Self::suffix_gain(owners@, i as int) == g { 1int } else { 0int }) == 0int);
                        assert(counts@[g] == old_counts[g]);
                        assert(Self::gain_count_from(owners@, g, i as int)
                            == Self::gain_count_from(owners@, g, i as int + 1) + 0int);
                    }
                };
                Self::lemma_suffix_bounds(owners@, i as int);
            }
        }
        proof {
            assert(i == 1);
        }
        counts
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn minimum_groups(owners: Vec<i64>, k: i64) -> (res: i64)
        requires
            2 <= owners.len() <= 200000,
            1 <= k <= 1000000000,
            forall|i: int| 0 <= i < owners.len() ==> #[trigger] owners@[i] == 0 || #[trigger] owners@[i] == 1,
        ensures
            res as int == Self::greedy_answer(owners@, k as int),
    {
        let n = owners.len();
        let counts = Solution::build_gain_counts(&owners);
        let mut gain: usize = n;
        let mut total: i64 = 0;
        let mut cuts: i64 = 0;
        while gain > 0 && total < k
            invariant
                counts.len() == n + 1,
                2 <= n <= 200000,
                n == owners@.len(),
                0 <= gain <= n,
                0 <= total <= 1_200_000_000i64,
                0 <= cuts,
                cuts as int <= (n as int - gain as int) * (n as int - 1),
                1 <= k <= 1000000000,
                forall|i: int| 0 <= i < owners@.len() ==> #[trigger] owners@[i] == 0 || #[trigger] owners@[i] == 1,
                forall|g: int| 1 <= g < counts.len() ==> #[trigger] counts@[g] as int == Self::gain_count_from(owners@, g, 1),
                Self::greedy_answer_rec(owners@, k as int, gain as int, total as int, cuts as int) == Self::greedy_answer(owners@, k as int),
            decreases gain,
        {
            let gain0 = gain;
            let gain_value = gain0 as i64;
            let total0 = total;
            let cuts0 = cuts;
            proof {
                assert(gain0 >= 1);
                assert(owners@.len() >= 2);
                assert(0 <= 1 && 1 <= owners@.len());
                Self::lemma_gain_count_bounds(owners@, gain0 as int, 1);
                assert(0 <= Self::gain_count_from(owners@, gain0 as int, 1) <= owners@.len() - 1);
                assert(1 <= gain0 as int);
                assert((gain0 as int) < counts.len());
                assert(counts@[gain0 as int] as int == Self::gain_count_from(owners@, gain0 as int, 1));
                assert(0 <= counts@[gain0 as int] as int <= n as int - 1);
            }
            let need = (k - total + gain_value - 1) / gain_value;
            let take = if counts[gain0] < need { counts[gain0] } else { need };
            proof {
                assert(0 <= take);
                assert(take <= n as i64 - 1);
                assert(0 <= take * gain_value) by(nonlinear_arith)
                    requires 0 <= take, 0 <= gain_value;
                assert(need * gain_value <= (k - total0) + gain_value - 1) by(nonlinear_arith)
                    requires
                        need as int == (k as int - total0 as int + gain_value as int - 1) / gain_value as int,
                        gain_value >= 1,
                        total0 < k;
                assert(take * gain_value <= need * gain_value) by(nonlinear_arith)
                    requires 0 <= take <= need, 0 <= gain_value;
                assert(take * gain_value <= (k - total0) + gain_value - 1);
                assert(total0 + take * gain_value <= k + gain_value - 1);
                assert(total0 + take * gain_value <= 1_200_000_000i64) by(nonlinear_arith)
                    requires
                        total0 + take * gain_value <= k + gain_value - 1,
                        k <= 1_000_000_000,
                        gain_value <= 200_000;
                assert((cuts0 + take) as int <= (n as int - (gain0 as int - 1)) * (n as int - 1)) by(nonlinear_arith)
                    requires
                        cuts0 as int <= (n as int - gain0 as int) * (n as int - 1),
                        0 <= take <= n as i64 - 1,
                        0 <= gain0 <= n,
                        n >= 2;
                assert((n as int - (gain0 as int - 1)) <= 200000) by(nonlinear_arith)
                    requires 0 <= gain0 as int - 1, n <= 200000;
                assert((n as int - 1) <= 199999) by(nonlinear_arith)
                    requires n <= 200000;
                assert((n as int - (gain0 as int - 1)) * (n as int - 1) < 40_000_000_000) by(nonlinear_arith)
                    requires
                        0 <= (n as int - (gain0 as int - 1)) <= 200000,
                        0 <= (n as int - 1) <= 199999;
            }
            total = total0 + take * gain_value;
            cuts = cuts0 + take;
            gain = gain0 - 1;
            proof {
                assert(gain_value as int == gain0 as int);
                assert(need as int == Self::ceil_div_pos(k as int - total0 as int, gain0 as int));
                assert(take as int == Self::min_int(counts@[gain0 as int] as int, need as int));
                assert(Self::greedy_answer_rec(
                    owners@,
                    k as int,
                    gain0 as int,
                    total0 as int,
                    cuts0 as int,
                ) == Self::greedy_answer_rec(owners@, k as int, gain as int, total as int, cuts as int));
            }
        }
        if total < k {
            proof {
                assert(gain == 0);
                assert(Self::greedy_answer_rec(owners@, k as int, 0, total as int, cuts as int) == -1);
            }
            -1
        } else {
            proof {
                assert(total >= k);
                assert(Self::greedy_answer_rec(owners@, k as int, gain as int, total as int, cuts as int) == cuts as int + 1);
            }
            assert(cuts + 1 <= i64::MAX) by {
                assert(cuts as int <= (n as int - gain as int) * (n as int - 1));
                assert((n as int - gain as int) * (n as int - 1) < 40_000_000_000) by(nonlinear_arith)
                    requires
                        0 <= gain <= n,
                        n <= 200000,
                        n >= 2;
            }
            cuts + 1
        }
    }
}

}