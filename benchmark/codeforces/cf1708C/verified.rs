use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn compute_ans(a: Seq<i64>, q: i64, i: int, cur_q: nat) -> Seq<u8>
        recommends 0 <= i <= a.len(),
        decreases i,
    {
        if i <= 0 {
            Seq::empty()
        } else {
            let idx = i - 1;
            if a[idx] <= cur_q {
                Self::compute_ans(a, q, idx, cur_q).push(1u8)
            } else if cur_q < q {
                Self::compute_ans(a, q, idx, cur_q + 1nat).push(1u8)
            } else {
                Self::compute_ans(a, q, idx, cur_q).push(0u8)
            }
        }
    }

    pub open spec fn solve(a: Seq<i64>, q: i64) -> Seq<u8> {
        Self::compute_ans(a, q, a.len() as int, 0nat)
    }

    pub open spec fn is_bits(ans: Seq<u8>) -> bool {
        forall|k: int| 0 <= k < ans.len() ==> (#[trigger] ans[k] == 0 || ans[k] == 1)
    }

    pub open spec fn count_ones_range(ans: Seq<u8>, i: int, end: int) -> int
        decreases end - i,
    {
        if i >= end {
            0
        } else {
            (if ans[i] == 1 { 1int } else { 0int }) + Self::count_ones_range(ans, i + 1, end)
        }
    }

    pub open spec fn min_budget_subset(a: Seq<i64>, ans: Seq<u8>, i: int) -> nat
        decreases a.len() - i,
    {
        if i >= a.len() {
            0
        } else {
            let rest = Self::min_budget_subset(a, ans, i + 1);
            if ans[i] == 0 {
                rest
            } else if a[i] as int <= rest as int {
                rest
            } else {
                (rest + 1) as nat
            }
        }
    }

    pub open spec fn canonical_cur_q(a: Seq<i64>, q: i64, i: int) -> nat
        decreases a.len() - i,
    {
        if i >= a.len() {
            0
        } else {
            let rest = Self::canonical_cur_q(a, q, i + 1);
            if a[i] as int <= rest as int {
                rest
            } else if (rest as int) < q {
                (rest + 1) as nat
            } else {
                rest
            }
        }
    }

    pub open spec fn forward_run(a: Seq<i64>, ans: Seq<u8>, i: int, iq: int) -> int
        decreases a.len() - i,
    {
        if i >= a.len() {
            iq
        } else if iq < 0 {
            -1
        } else if ans[i] == 0 {
            Self::forward_run(a, ans, i + 1, iq)
        } else if iq <= 0 {
            -1
        } else if a[i] as int > iq {
            Self::forward_run(a, ans, i + 1, iq - 1)
        } else {
            Self::forward_run(a, ans, i + 1, iq)
        }
    }

    proof fn lemma_min_budget_at_least_one_when_tested(a: Seq<i64>, ans: Seq<u8>, i: int)
        requires
            a.len() == ans.len(),
            0 <= i < a.len(),
            Self::is_bits(ans),
            ans[i] == 1,
            forall|k: int| 0 <= k < a.len() ==> a[k] >= 1,
        ensures
            Self::min_budget_subset(a, ans, i) >= 1,
    {
        let rest = Self::min_budget_subset(a, ans, i + 1);
        assert(a[i] >= 1);
    }

    proof fn lemma_budget_suffices(a: Seq<i64>, ans: Seq<u8>, i: int, budget: int)
        requires
            a.len() == ans.len(),
            0 <= i <= a.len(),
            Self::is_bits(ans),
            forall|k: int| 0 <= k < a.len() ==> a[k] >= 1,
            budget >= Self::min_budget_subset(a, ans, i) as int,
        ensures
            Self::forward_run(a, ans, i, budget) >= 0,
        decreases a.len() - i,
    {
        if i >= a.len() {
        } else {
            let rest = Self::min_budget_subset(a, ans, i + 1);
            if ans[i] == 0 {
                Self::lemma_budget_suffices(a, ans, i + 1, budget);
            } else {
                Self::lemma_min_budget_at_least_one_when_tested(a, ans, i);
                if a[i] as int <= rest {
                    Self::lemma_budget_suffices(a, ans, i + 1, budget);
                } else {
                    if a[i] as int <= budget {
                        Self::lemma_budget_suffices(a, ans, i + 1, budget);
                    } else {
                        Self::lemma_budget_suffices(a, ans, i + 1, budget - 1);
                    }
                }
            }
        }
    }

    proof fn lemma_budget_necessary(a: Seq<i64>, ans: Seq<u8>, i: int, budget: int)
        requires
            a.len() == ans.len(),
            0 <= i <= a.len(),
            Self::is_bits(ans),
            forall|k: int| 0 <= k < a.len() ==> a[k] >= 1,
            Self::forward_run(a, ans, i, budget) >= 0,
        ensures
            budget >= Self::min_budget_subset(a, ans, i) as int,
        decreases a.len() - i,
    {
        if i >= a.len() {
        } else {
            let rest = Self::min_budget_subset(a, ans, i + 1);
            if ans[i] == 0 {
                Self::lemma_budget_necessary(a, ans, i + 1, budget);
            } else {
                assert(budget > 0);
                if a[i] as int > budget {
                    Self::lemma_budget_necessary(a, ans, i + 1, budget - 1);
                } else {
                    Self::lemma_budget_necessary(a, ans, i + 1, budget);
                }
            }
        }
    }

    proof fn lemma_canonical_cur_q_le_q(a: Seq<i64>, q: i64, i: int)
        requires
            0 <= i <= a.len(),
            1 <= q,
        ensures
            Self::canonical_cur_q(a, q, i) as int <= q as int,
        decreases a.len() - i,
    {
        if i >= a.len() {
        } else {
            Self::lemma_canonical_cur_q_le_q(a, q, i + 1);
        }
    }

    proof fn lemma_len(a: Seq<i64>, q: i64, i: int, cur_q: nat)
        requires
            0 <= i <= a.len(),
        ensures
            Self::compute_ans(a, q, i, cur_q).len() == i,
        decreases i,
    {
        if i <= 0 {
        } else {
            let idx = i - 1;
            if a[idx] <= cur_q {
                Self::lemma_len(a, q, idx, cur_q);
            } else if cur_q < q {
                Self::lemma_len(a, q, idx, (cur_q + 1) as nat);
            } else {
                Self::lemma_len(a, q, idx, cur_q);
            }
        }
    }

    proof fn lemma_unfold(a: Seq<i64>, q: i64, n: int, i: int)
        requires
            a.len() == n,
            0 <= i <= n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
        ensures
            Self::compute_ans(a, q, n, 0nat).subrange(0, i)
                =~= Self::compute_ans(a, q, i, Self::canonical_cur_q(a, q, i)),
        decreases n - i,
    {
        Self::lemma_len(a, q, n, 0nat);
        if i >= n {
            assert(Self::compute_ans(a, q, n, 0nat).subrange(0, n) =~= Self::compute_ans(a, q, n, 0nat));
            assert(Self::canonical_cur_q(a, q, n) == 0);
        } else {
            Self::lemma_unfold(a, q, n, i + 1);
            Self::lemma_len(a, q, i + 1, Self::canonical_cur_q(a, q, i + 1));
            let rest = Self::canonical_cur_q(a, q, i + 1);
            let whole_prefix_ip1 = Self::compute_ans(a, q, n, 0nat).subrange(0, i + 1);
            assert(whole_prefix_ip1 =~= Self::compute_ans(a, q, i + 1, rest));
            if a[i] as int <= rest as int {
                assert(Self::compute_ans(a, q, i + 1, rest)
                    =~= Self::compute_ans(a, q, i, rest).push(1u8));
                assert(Self::canonical_cur_q(a, q, i) == rest);
                Self::lemma_len(a, q, i, rest);
            } else if (rest as int) < q {
                assert(Self::compute_ans(a, q, i + 1, rest)
                    =~= Self::compute_ans(a, q, i, (rest + 1) as nat).push(1u8));
                assert(Self::canonical_cur_q(a, q, i) == (rest + 1) as nat);
                Self::lemma_len(a, q, i, (rest + 1) as nat);
            } else {
                assert(Self::compute_ans(a, q, i + 1, rest)
                    =~= Self::compute_ans(a, q, i, rest).push(0u8));
                assert(Self::canonical_cur_q(a, q, i) == rest);
                Self::lemma_len(a, q, i, rest);
            }
            assert(Self::compute_ans(a, q, n, 0nat).subrange(0, i)
                =~= whole_prefix_ip1.subrange(0, i));
        }
    }

    proof fn lemma_g_bit_rule(a: Seq<i64>, q: i64, n: int, i: int)
        requires
            a.len() == n,
            0 <= i < n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
        ensures
            ({
                let g = Self::compute_ans(a, q, n, 0nat);
                let rest = Self::canonical_cur_q(a, q, i + 1);
                &&& (a[i] as int <= rest as int ==> g[i] == 1)
                &&& (a[i] as int > rest as int && (rest as int) < q ==> g[i] == 1)
                &&& (a[i] as int > rest as int && (rest as int) >= q ==> g[i] == 0)
                &&& Self::canonical_cur_q(a, q, i) == (if a[i] as int <= rest as int {
                    rest
                } else if (rest as int) < q {
                    (rest + 1) as nat
                } else {
                    rest
                })
            }),
    {
        Self::lemma_unfold(a, q, n, i + 1);
        Self::lemma_unfold(a, q, n, i);
        Self::lemma_len(a, q, i + 1, Self::canonical_cur_q(a, q, i + 1));
        Self::lemma_len(a, q, i, Self::canonical_cur_q(a, q, i));
        Self::lemma_len(a, q, n, 0nat);
        let g = Self::compute_ans(a, q, n, 0nat);
        let rest = Self::canonical_cur_q(a, q, i + 1);
        let whole_prefix_ip1 = g.subrange(0, i + 1);
        assert(whole_prefix_ip1 =~= Self::compute_ans(a, q, i + 1, rest));
        if a[i] as int <= rest as int {
            assert(Self::compute_ans(a, q, i + 1, rest)
                =~= Self::compute_ans(a, q, i, rest).push(1u8));
        } else if (rest as int) < q {
            assert(Self::compute_ans(a, q, i + 1, rest)
                =~= Self::compute_ans(a, q, i, (rest + 1) as nat).push(1u8));
        } else {
            assert(Self::compute_ans(a, q, i + 1, rest)
                =~= Self::compute_ans(a, q, i, rest).push(0u8));
        }
        assert(g[i] == whole_prefix_ip1[i]);
    }

    proof fn lemma_g_consistent(a: Seq<i64>, q: i64, n: int, i: int)
        requires
            a.len() == n,
            0 <= i <= n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
        ensures
            Self::canonical_cur_q(a, q, i) == Self::min_budget_subset(a, Self::compute_ans(a, q, n, 0nat), i),
        decreases n - i,
    {
        let g = Self::compute_ans(a, q, n, 0nat);
        if i >= n {
        } else {
            Self::lemma_g_consistent(a, q, n, i + 1);
            Self::lemma_g_bit_rule(a, q, n, i);
            let rest = Self::canonical_cur_q(a, q, i + 1);
        }
    }

    proof fn lemma_min_budget_monotone(a: Seq<i64>, ans: Seq<u8>, i: int)
        requires
            0 <= i <= a.len(),
        ensures
            Self::min_budget_subset(a, ans, i) as int >= Self::min_budget_subset(a, ans, i + 1) as int,
        decreases a.len() - i,
    {
    }

    proof fn lemma_property2(a: Seq<i64>, q: i64, n: int, i: int, other: Seq<u8>)
        requires
            a.len() == n,
            0 <= i <= n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
            other.len() == n,
            Self::is_bits(other),
            Self::min_budget_subset(a, other, i) as int <= q as int,
        ensures
            Self::min_budget_subset(a, other, i) as int
                <= Self::min_budget_subset(a, Self::compute_ans(a, q, n, 0nat), i) as int,
        decreases n - i,
    {
        let g = Self::compute_ans(a, q, n, 0nat);
        if i >= n {
        } else {
            Self::lemma_min_budget_monotone(a, other, i);
            let rest_o = Self::min_budget_subset(a, other, i + 1);
            let rest_g = Self::min_budget_subset(a, g, i + 1);
            assert(rest_o as int <= q as int);
            Self::lemma_property2(a, q, n, i + 1, other);
            Self::lemma_g_consistent(a, q, n, i + 1);
            Self::lemma_g_bit_rule(a, q, n, i);
            let canon_rest = Self::canonical_cur_q(a, q, i + 1);
            assert(canon_rest == rest_g);

            if other[i] == 0 {
                assert(Self::min_budget_subset(a, other, i) == rest_o);
                assert(rest_o as int <= rest_g as int);
                assert(rest_g as int <= Self::min_budget_subset(a, g, i) as int) by {
                    Self::lemma_min_budget_monotone(a, g, i);
                };
            } else if a[i] as int <= rest_o as int {
                assert(Self::min_budget_subset(a, other, i) == rest_o);
                assert(rest_g as int <= Self::min_budget_subset(a, g, i) as int) by {
                    Self::lemma_min_budget_monotone(a, g, i);
                };
            } else {
                assert(Self::min_budget_subset(a, other, i) == (rest_o + 1) as nat);
                assert((rest_o + 1) as int <= q as int);
                if (rest_o as int) < (rest_g as int) {
                    assert((rest_o + 1) as int <= rest_g as int);
                    assert(rest_g as int <= Self::min_budget_subset(a, g, i) as int) by {
                        Self::lemma_min_budget_monotone(a, g, i);
                    };
                } else {
                    assert(rest_o == rest_g);
                    assert(a[i] as int > rest_g as int);
                    assert((rest_o as int) < q as int);
                    assert((rest_g as int) < q as int);
                    assert(Self::min_budget_subset(a, g, i) == (rest_g + 1) as nat);
                }
            }
        }
    }

    proof fn lemma_g_net_monotone(a: Seq<i64>, q: i64, n: int, i: int)
        requires
            a.len() == n,
            0 <= i < n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
        ensures
            ({
                let g = Self::compute_ans(a, q, n, 0nat);
                Self::count_ones_range(g, i, n) as int - Self::min_budget_subset(a, g, i) as int
                    >= Self::count_ones_range(g, i + 1, n) as int - Self::min_budget_subset(a, g, i + 1) as int
            }),
    {
        let g = Self::compute_ans(a, q, n, 0nat);
        Self::lemma_len(a, q, n, 0nat);
        Self::lemma_g_consistent(a, q, n, i + 1);
        Self::lemma_g_bit_rule(a, q, n, i);
        let rest = Self::canonical_cur_q(a, q, i + 1);
        assert(Self::count_ones_range(g, i, n) as int
            == Self::count_ones_range(g, i + 1, n) as int + (if g[i] == 1 { 1int } else { 0int }));
    }

    proof fn lemma_property1(a: Seq<i64>, q: i64, n: int, i: int, other: Seq<u8>)
        requires
            a.len() == n,
            0 <= i <= n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
            other.len() == n,
            Self::is_bits(other),
            Self::min_budget_subset(a, other, i) as int <= q as int,
        ensures
            ({
                let g = Self::compute_ans(a, q, n, 0nat);
                Self::count_ones_range(other, i, n) as int - Self::min_budget_subset(a, other, i) as int
                    <= Self::count_ones_range(g, i, n) as int - Self::min_budget_subset(a, g, i) as int
            }),
        decreases n - i,
    {
        let g = Self::compute_ans(a, q, n, 0nat);
        if i >= n {
        } else {
            Self::lemma_min_budget_monotone(a, other, i);
            let rest_o = Self::min_budget_subset(a, other, i + 1);
            let rest_g = Self::min_budget_subset(a, g, i + 1);
            assert(rest_o as int <= q as int);
            Self::lemma_property1(a, q, n, i + 1, other);
            Self::lemma_property2(a, q, n, i + 1, other);
            Self::lemma_g_net_monotone(a, q, n, i);
            Self::lemma_g_consistent(a, q, n, i + 1);
            Self::lemma_g_bit_rule(a, q, n, i);
            let canon_rest = Self::canonical_cur_q(a, q, i + 1);

            if other[i] == 0 {
                assert(Self::min_budget_subset(a, other, i) == rest_o);
                assert(Self::count_ones_range(other, i, n) == Self::count_ones_range(other, i + 1, n));
            } else if a[i] as int <= rest_o as int {
                assert(Self::min_budget_subset(a, other, i) == rest_o);
                assert(Self::count_ones_range(other, i, n) == 1 + Self::count_ones_range(other, i + 1, n));
                assert(a[i] as int <= rest_g as int);
                assert(g[i] == 1);
                assert(Self::min_budget_subset(a, g, i) == rest_g);
                assert(Self::count_ones_range(g, i, n) == 1 + Self::count_ones_range(g, i + 1, n));
            } else {
                assert(Self::min_budget_subset(a, other, i) == (rest_o + 1) as nat);
                assert(Self::count_ones_range(other, i, n) == 1 + Self::count_ones_range(other, i + 1, n));
                assert((rest_o + 1) as int <= q as int);
            }
        }
    }

    proof fn lemma_g_feasible(a: Seq<i64>, q: i64, n: int)
        requires
            a.len() == n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
        ensures
            Self::forward_run(a, Self::compute_ans(a, q, n, 0nat), 0, q as int) >= 0,
    {
        let g = Self::compute_ans(a, q, n, 0nat);
        Self::lemma_len(a, q, n, 0nat);
        Self::lemma_g_consistent(a, q, n, 0);
        Self::lemma_canonical_cur_q_le_q(a, q, 0);
        assert(Self::min_budget_subset(a, g, 0) as int <= q as int);
        assert forall|k: int| 0 <= k < g.len() implies (#[trigger] g[k] == 0 || g[k] == 1) by {
            Self::lemma_g_bit_rule_bits(a, q, n, k);
        };
        Self::lemma_budget_suffices(a, g, 0, q as int);
    }

    proof fn lemma_g_bit_rule_bits(a: Seq<i64>, q: i64, n: int, i: int)
        requires
            a.len() == n,
            0 <= i < n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
        ensures
            ({
                let g = Self::compute_ans(a, q, n, 0nat);
                g[i] == 0 || g[i] == 1
            }),
    {
        Self::lemma_len(a, q, n, 0nat);
        Self::lemma_g_bit_rule(a, q, n, i);
    }

    proof fn lemma_g_optimal(a: Seq<i64>, q: i64, n: int, other: Seq<u8>)
        requires
            a.len() == n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
            other.len() == n,
            Self::is_bits(other),
            Self::forward_run(a, other, 0, q as int) >= 0,
        ensures
            ({
                let g = Self::compute_ans(a, q, n, 0nat);
                Self::count_ones_range(other, 0, n) <= Self::count_ones_range(g, 0, n)
            }),
    {
        let g = Self::compute_ans(a, q, n, 0nat);
        Self::lemma_len(a, q, n, 0nat);
        Self::lemma_budget_necessary(a, other, 0, q as int);
        assert(Self::min_budget_subset(a, other, 0) as int <= q as int);
        Self::lemma_property1(a, q, n, 0, other);
        Self::lemma_property2(a, q, n, 0, other);
    }

    pub fn optimal_tests(a: Vec<i64>, q: i64) -> (ans: Vec<u8>)
        requires
            1 <= a.len() <= 100_000,
            1 <= q <= 1_000_000_000,
            forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
        ensures
            ans@.len() == a@.len(),
            Self::is_bits(ans@),
            Self::forward_run(a@, ans@, 0, q as int) >= 0,
            forall|other: Seq<u8>|
                other.len() == a@.len() && Self::is_bits(other) && Self::forward_run(a@, other, 0, q as int) >= 0
                    ==> #[trigger] Self::count_ones_range(other, 0, a@.len() as int)
                        <= Self::count_ones_range(ans@, 0, a@.len() as int),
    {
        let n = a.len();
        let mut cur_q: i64 = 0;
        let mut ans: Vec<u8> = Vec::new();
        let mut fill: usize = 0;
        while fill < n
            invariant
                n == a.len(),
                0 <= fill <= n,
                ans.len() == fill,
                forall |k: int| 0 <= k < fill ==> ans@[k] == 0,
            decreases n - fill,
        {
            ans.push(0);
            fill = fill + 1;
        }

        let mut i: usize = n;
        while i > 0
            invariant
                1 <= n <= 100_000,
                n == a.len(),
                ans.len() == n,
                0 <= i <= n,
                0 <= cur_q <= q,
                Self::solve(a@, q) =~= Self::compute_ans(a@, q, i as int, cur_q as nat) + ans@.subrange(i as int, n as int),
            decreases i,
        {
            i = i - 1;
            let aval = a[i];

            if aval <= cur_q {
                ans[i] = 1;
                proof {
                    assert(Self::compute_ans(a@, q, (i + 1) as int, cur_q as nat) =~= Self::compute_ans(a@, q, i as int, cur_q as nat).push(1u8));
                }
            } else if cur_q < q {
                cur_q = cur_q + 1;
                ans[i] = 1;
                proof {
                    assert(Self::compute_ans(a@, q, (i + 1) as int, (cur_q - 1) as nat) =~= Self::compute_ans(a@, q, i as int, cur_q as nat).push(1u8));
                }
            } else {
                ans[i] = 0;
                proof {
                    assert(Self::compute_ans(a@, q, (i + 1) as int, cur_q as nat) =~= Self::compute_ans(a@, q, i as int, cur_q as nat).push(0u8));
                }
            }
        }

        proof {
            assert(ans@.subrange(0, n as int) =~= ans@);
            assert(Self::compute_ans(a@, q, 0, cur_q as nat) =~= Seq::empty());
            assert(ans@ =~= Self::solve(a@, q));
            assert(forall|k: int| 0 <= k < a@.len() ==> a@[k] >= 1);
            Self::lemma_g_feasible(a@, q, n as int);
            assert forall|other: Seq<u8>|
                other.len() == a@.len() && Self::is_bits(other) && Self::forward_run(a@, other, 0, q as int) >= 0
                implies #[trigger] Self::count_ones_range(other, 0, a@.len() as int)
                    <= Self::count_ones_range(ans@, 0, a@.len() as int) by {
                Self::lemma_g_optimal(a@, q, n as int, other);
            };
            Self::lemma_g_bit_rule_ans_bits(a@, q, n as int, ans@);
        }

        ans
    }

    proof fn lemma_g_bit_rule_ans_bits(a: Seq<i64>, q: i64, n: int, ans: Seq<u8>)
        requires
            a.len() == n,
            1 <= q,
            forall|k: int| 0 <= k < n ==> a[k] >= 1,
            ans =~= Self::compute_ans(a, q, n, 0nat),
        ensures
            Self::is_bits(ans),
    {
        Self::lemma_len(a, q, n, 0nat);
        assert forall|k: int| 0 <= k < ans.len() implies (#[trigger] ans[k] == 0 || ans[k] == 1) by {
            Self::lemma_g_bit_rule_bits(a, q, n, k);
        };
    }
}

}
