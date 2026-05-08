use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub closed spec fn sum_seq(s: Seq<i32>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::sum_seq(s.drop_last()) + s.last() as int
        }
    }

    pub open spec fn prefix_sum(s: Seq<i32>, k: int) -> int
        recommends 0 <= k <= s.len()
        decreases k
    {
        if k <= 0 { 0 }
        else { Self::prefix_sum(s, k - 1) + s[k - 1] as int }
    }

    pub open spec fn running_deficit(s: Seq<i32>, avg: int, i: int) -> int
        recommends 0 <= i < s.len()
    {
        Self::prefix_sum(s, i + 1) - avg * (i + 1)
    }

    pub open spec fn abs(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn trig(x: int) -> int { x }

    pub open spec fn feasible_k(machines: Seq<i32>, avg: int, k: int) -> bool {
        let n = machines.len() as int;
        k >= 0
        && (forall|i: int| 0 <= i < n ==> k >= machines[i] as int - avg)
        && (forall|i: int| 0 <= i < n ==> k >= Self::abs(Self::running_deficit(machines, avg, i)))
    }

    pub open spec fn spec_answer(machines: Seq<i32>, avg: int) -> int {
        choose|k: int|
            Self::feasible_k(machines, avg, k)
            && #[trigger] Self::trig(k) == k
            && (forall|k2: int|
                Self::feasible_k(machines, avg, k2)
                && #[trigger] Self::trig(k2) == k2
                ==> k <= k2)
    }

    fn max_i64(a: i64, b: i64) -> (r: i64)
        ensures
            r >= a,
            r >= b,
    {
        if a >= b { a } else { b }
    }

    fn abs_i64(x: i64) -> (r: i64)
        ensures
            r >= 0,
    {
        if x >= 0 {
            x
        } else if x == -9223372036854775808i64 {
            0
        } else {
            -x
        }
    }

    fn nonneg_i32_to_usize(x: i32) -> (u: usize)
        requires
            x >= 0,
        ensures
            u as int == x as int,
    {
        x as usize
    }

    proof fn lemma_sum_seq_prefix_step(s: Seq<i32>, i: int)
        requires
            0 <= i < s.len(),
        ensures
            Self::sum_seq(s.subrange(0, i + 1)) == Self::sum_seq(s.subrange(0, i)) + s[i] as int,
    {
        assert(s.subrange(0, i + 1) == s.subrange(0, i).push(s[i]));
        assert(s.subrange(0, i + 1).drop_last() == s.subrange(0, i));
        assert(s.subrange(0, i + 1).last() == s[i]);
    }

    proof fn lemma_prefix_sum_step(s: Seq<i32>, i: int)
        requires
            0 <= i < s.len(),
        ensures
            Self::prefix_sum(s, i + 1) == Self::prefix_sum(s, i) + s[i] as int,
    {
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn find_min_moves(machines: Vec<i32>) -> (result: i32)
        requires
            1 <= machines.len() <= 10000,
            forall|i: int| 0 <= i < machines.len() ==> 0 <= #[trigger] machines[i] <= 100000,
        ensures
            result >= -1,
            Self::sum_seq(machines@) % (machines.len() as int) != 0 ==> result == -1,
            Self::sum_seq(machines@) % (machines.len() as int) == 0 ==>
                result as int == Self::spec_answer(
                    machines@,
                    Self::sum_seq(machines@) / (machines.len() as int),
                ),
    {
        let n = machines.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == machines.len(),
                1 <= n <= 10000,
                i <= n,
                forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] machines[k] <= 100000,
                total as int == Self::sum_seq(machines@.subrange(0, i as int)),
                0 <= total as int <= 100000 * i as int,
        {
            proof { assert(i < n); }
            let old_i = i;
            let old_total = total;
            proof {
                assert(0 <= old_i as int);
                assert((old_i as int) < (n as int));
                assert(0 <= machines[old_i as int] as int <= 100000);
                assert(0 <= old_total as int <= 100000 * old_i as int);
                assert((old_i as int) < 10000) by (nonlinear_arith)
                    requires
                    (old_i as int) < (n as int),
                    (n as int) <= 10000,
                {};
                assert(old_total as int + machines[old_i as int] as int <= 100000 * (old_i as int + 1)) by (nonlinear_arith)
                    requires
                        old_total as int <= 100000 * old_i as int,
                        machines[old_i as int] as int <= 100000,
                {};
                assert(old_total as int + machines[old_i as int] as int <= 100000 * 10000) by (nonlinear_arith)
                    requires
                        old_total as int + machines[old_i as int] as int <= 100000 * (old_i as int + 1),
                        (old_i as int) < 10000,
                {};
                assert(100000 * 10000 < i64::MAX as int) by (nonlinear_arith);
            }
            total = total + machines[i] as i64;
            proof {
                assert(0 <= old_i as int);
                assert((old_i as int) < (n as int));
                assert(total as int == old_total as int + machines[old_i as int] as int);
                Self::lemma_sum_seq_prefix_step(machines@, old_i as int);
                assert(0 <= machines[old_i as int] as int <= 100000);
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(machines@.subrange(0, i as int) == machines@);
            assert(total as int == Self::sum_seq(machines@));
        }

        if total % n as i64 != 0 {
            return -1;
        }

        let avg = total / n as i64;
        proof {
            assert(0 <= total as int <= 100000 * n as int);
            assert(1 <= n as int);
            assert(avg as int == (total as int) / (n as int));
            assert(0 <= avg as int <= 100000) by (nonlinear_arith)
                requires
                    0 <= total as int <= 100000 * n as int,
                    1 <= n as int,
                    avg as int == (total as int) / (n as int),
            {};
        }
        proof {
            assert(1 <= n as int <= 10000);
            assert(0 <= total as int <= 100000 * n as int);
            assert(avg as int == total as int / (n as int));
            assert(0 <= avg as int <= 100000) by (nonlinear_arith)
                requires
                    1 <= n as int,
                    0 <= total as int <= 100000 * n as int,
                    avg as int == total as int / (n as int),
            {};
        }

        let mut balance: i64 = 0;
        let mut res: i64 = 0;
        i = 0;
        while i < n
            invariant
                n == machines.len(),
                1 <= n <= 10000,
                i <= n,
                0 <= avg as int <= 100000,
                forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] machines[k] <= 100000,
                balance as int == Self::prefix_sum(machines@, i as int) - (avg as int) * (i as int),
                -100000 * i as int <= balance as int <= 100000 * i as int,
                0 <= res as int,
                res as int <= 100000 * n as int,
                forall|j: int| 0 <= j < i as int ==> res as int >= machines[j] as int - (avg as int),
                forall|j: int| 0 <= j < i as int ==> res as int >= #[trigger] Self::abs(Self::running_deficit(machines@, avg as int, j)),
                forall|k2: int|
                    Self::feasible_k(machines@, avg as int, k2)
                    && #[trigger] Self::trig(k2) == k2
                    ==> res as int <= k2,
        {
            let old_i = i;
            let old_balance = balance;
            let old_res = res;

            let diff = machines[i] as i64 - avg;
            balance = balance + diff;
            let abs_bal = if balance >= 0 { balance } else { -balance };
            let need = if abs_bal >= diff { abs_bal } else { diff };
            res = if res >= need { res } else { need };
            i += 1;

            proof {
                assert(0 <= old_i as int);
                assert((old_i as int) < (n as int));
                assert(i as int == old_i as int + 1);
                assert(0 <= machines[old_i as int] as int <= 100000);
                assert(diff as int == machines[old_i as int] as int - (avg as int));
                assert(diff as int <= 100000) by (nonlinear_arith)
                    requires
                        0 <= machines[old_i as int] as int <= 100000,
                        0 <= avg as int <= 100000,
                        diff as int == machines[old_i as int] as int - (avg as int),
                {};
                assert(-100000 <= diff as int) by (nonlinear_arith)
                    requires
                        0 <= machines[old_i as int] as int <= 100000,
                        0 <= avg as int <= 100000,
                        diff as int == machines[old_i as int] as int - (avg as int),
                {};
                assert(-100000 <= diff as int <= 100000);
                Self::lemma_prefix_sum_step(machines@, old_i as int);
                assert(Self::prefix_sum(machines@, i as int)
                    == Self::prefix_sum(machines@, old_i as int) + machines[old_i as int] as int);
                assert(old_balance as int == Self::prefix_sum(machines@, old_i as int) - (avg as int) * (old_i as int));
                assert(balance as int == old_balance as int + diff as int);
                assert(balance as int
                    == (Self::prefix_sum(machines@, old_i as int) - (avg as int) * (old_i as int))
                     + (machines[old_i as int] as int - (avg as int)));
                assert((avg as int) * (old_i as int + 1)
                    == (avg as int) * (old_i as int) + (avg as int)) by (nonlinear_arith);
                assert(balance as int
                    == Self::prefix_sum(machines@, old_i as int)
                        + machines[old_i as int] as int
                        - ((avg as int) * (old_i as int) + (avg as int)));
                assert(balance as int
                    == Self::prefix_sum(machines@, old_i as int)
                        + machines[old_i as int] as int
                        - (avg as int) * (old_i as int + 1));
                assert(balance as int == Self::prefix_sum(machines@, old_i as int + 1) - (avg as int) * (old_i as int + 1));
                assert(balance as int == Self::prefix_sum(machines@, i as int) - (avg as int) * (i as int));
                assert(Self::running_deficit(machines@, avg as int, old_i as int) == balance as int);
                assert(-100000 * (old_i as int + 1) <= balance as int) by (nonlinear_arith)
                    requires
                        -100000 * old_i as int <= old_balance as int,
                        -100000 <= diff as int,
                        balance as int == old_balance as int + diff as int,
                {};
                assert(balance as int <= 100000 * (old_i as int + 1)) by (nonlinear_arith)
                    requires
                        old_balance as int <= 100000 * old_i as int,
                        diff as int <= 100000,
                        balance as int == old_balance as int + diff as int,
                {};
                assert(-100000 * (old_i as int + 1) <= balance as int <= 100000 * (old_i as int + 1));
                assert(-100000 * i as int <= balance as int <= 100000 * i as int);

                assert(need >= 0);
                assert(res >= need);
                assert(0 <= res as int);
                assert(-100000 * n as int <= balance as int <= 100000 * n as int) by (nonlinear_arith)
                    requires
                        -100000 * i as int <= balance as int <= 100000 * i as int,
                        i as int <= n as int,
                {};
                assert(abs_bal as int <= 100000 * n as int) by {
                    if balance >= 0 {
                        assert(abs_bal == balance);
                    } else {
                        assert(abs_bal == -balance);
                        assert(-balance as int <= 100000 * n as int) by (nonlinear_arith)
                            requires
                                -100000 * n as int <= balance as int,
                        {};
                    }
                };
                assert(need as int <= 100000 * n as int) by {
                    if abs_bal >= diff {
                        assert(need == abs_bal);
                    } else {
                        assert(need == diff);
                        assert(diff as int <= 100000 * n as int) by (nonlinear_arith)
                            requires
                                diff as int <= 100000,
                                1 <= n as int,
                        {};
                    }
                }
                assert(res as int <= 100000 * n as int) by {
                    if old_res >= need {
                        assert(res == old_res);
                    } else {
                        assert(res == need);
                    }
                }

                assert(res as int >= old_res as int);
                assert(forall|j: int| 0 <= j < old_i as int ==> res as int >= #[trigger] Self::abs(Self::running_deficit(machines@, avg as int, j))) by {
                    assert(res as int >= old_res as int);
                };
                assert(res as int >= Self::abs(Self::running_deficit(machines@, avg as int, old_i as int))) by {
                    assert(Self::running_deficit(machines@, avg as int, old_i as int) == balance as int);
                    if balance >= 0 {
                        assert(abs_bal == balance);
                        assert(Self::abs(balance as int) == balance as int);
                    } else {
                        assert(abs_bal == -balance);
                        assert(Self::abs(balance as int) == -(balance as int));
                    }
                    assert(abs_bal as int == Self::abs(balance as int));
                    if abs_bal >= diff {
                        assert(need == abs_bal);
                    } else {
                        assert(need == diff);
                    }
                    assert(res >= need);
                };

                assert forall|k2: int|
                    Self::feasible_k(machines@, avg as int, k2)
                    && #[trigger] Self::trig(k2) == k2
                    implies res as int <= k2 by {
                    if Self::feasible_k(machines@, avg as int, k2)
                        && #[trigger] Self::trig(k2) == k2 {
                        assert(old_res as int <= k2);
                        assert(k2 >= Self::abs(Self::running_deficit(machines@, avg as int, old_i as int)));
                        assert(Self::running_deficit(machines@, avg as int, old_i as int) == balance as int);
                        assert(k2 >= abs_bal as int);
                        assert(k2 >= diff as int);
                        assert(k2 >= need as int) by {
                            if abs_bal >= diff {
                                assert(need == abs_bal);
                            } else {
                                assert(need == diff);
                            }
                        };
                        assert(res as int <= k2) by {
                            if old_res >= need {
                                assert(res == old_res);
                            } else {
                                assert(res == need);
                            }
                        };
                    }
                };
            }
        }

        proof {
            assert(avg as int == Self::sum_seq(machines@) / (n as int));
            assert(i == n);
            assert(0 <= res as int);
            assert(forall|j: int| 0 <= j < n as int ==> res as int >= machines[j] as int - (avg as int));
            assert(forall|j: int| 0 <= j < n as int ==> res as int >= #[trigger] Self::abs(Self::running_deficit(machines@, avg as int, j)));
            assert(Self::feasible_k(machines@, avg as int, res as int));

            assert(exists|k: int|
                Self::feasible_k(machines@, avg as int, k)
                && #[trigger] Self::trig(k) == k
                && (forall|k2: int|
                    Self::feasible_k(machines@, avg as int, k2)
                    && #[trigger] Self::trig(k2) == k2
                    ==> k <= k2)
            ) by {
                let k = res as int;
                assert(Self::feasible_k(machines@, avg as int, k));
                assert(Self::trig(k) == k);
                assert(forall|k2: int|
                    Self::feasible_k(machines@, avg as int, k2)
                    && #[trigger] Self::trig(k2) == k2
                    ==> k <= k2);
            }

            let sa = Self::spec_answer(machines@, avg as int);
            assert(Self::feasible_k(machines@, avg as int, sa));
            assert(Self::trig(sa) == sa);
            assert(forall|k2: int|
                Self::feasible_k(machines@, avg as int, k2)
                && #[trigger] Self::trig(k2) == k2
                ==> sa <= k2);
            assert(Self::trig(res as int) == res as int);
            assert(sa <= res as int);
            assert(res as int <= sa);
            assert(res as int == Self::spec_answer(machines@, avg as int));
            assert(res as int == Self::spec_answer(machines@, Self::sum_seq(machines@) / (n as int)));

            assert(100000 * n as int <= 100000 * 10000) by (nonlinear_arith)
                requires
                    n as int <= 10000,
            {};
            assert(100000 * 10000 < 2147483647) by (nonlinear_arith);
            assert((res as int) < 2147483647) by (nonlinear_arith)
                requires
                    res as int <= 100000 * n as int,
                    100000 * n as int <= 100000 * 10000,
                    100000 * 10000 < 2147483647,
            {};
        }

        res as i32
    }
}

}
