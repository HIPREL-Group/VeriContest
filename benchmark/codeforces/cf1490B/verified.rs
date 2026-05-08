use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn rem3(x: i32) -> int {
    let m = x as int % 3;
    if m < 0 {
        m + 3
    } else {
        m
    }
}

pub open spec fn count_rem_prefix(a: Seq<i32>, r: int, idx: int) -> int
    decreases idx,
{
    if idx <= 0 {
        0
    } else {
        (if rem3(a[idx - 1]) == r {
            1int
        } else {
            0int
        }) + count_rem_prefix(a, r, idx - 1)
    }
}

pub open spec fn count_rem(a: Seq<i32>, r: int) -> int {
    count_rem_prefix(a, r, a.len() as int)
}

pub open spec fn min_balance_ops_f(c0: int, c1: int, c2: int, tgt: int, fuel: nat) -> int
    recommends
        c0 + c1 + c2 == 3 * tgt,
    decreases fuel,
{
    if c0 == tgt && c1 == tgt && c2 == tgt {
        0
    } else if fuel == 0 {
        0
    } else if c0 > tgt {
        1 + min_balance_ops_f(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat)
    } else if c1 > tgt {
        1 + min_balance_ops_f(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat)
    } else {
        1 + min_balance_ops_f(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat)
    }
}

proof fn lemma_i32_rem3_nonneg(x: i32)
    requires
        x >= 0,
    ensures
        x as int % 3 == rem3(x),
        0 <= rem3(x) <= 2,
        (x % 3) as int == rem3(x),
{
    let m = x as int % 3;
    assert(m >= 0) by {
        assert(x as int >= 0);
    };
    assert(rem3(x) == m);
    assert(0 <= m && m < 3);
    assert((x % 3) as int == m);
}

proof fn lemma_count_prefix_split(a: Seq<i32>, r: int, idx: int)
    requires
        0 < idx <= a.len(),
    ensures
        count_rem_prefix(a, r, idx) == count_rem_prefix(a, r, idx - 1)
            + (if rem3(a[idx - 1]) == r {
                1int
            } else {
                0int
            }),
{
}

proof fn lemma_count_prefix_nonneg(a: Seq<i32>, r: int, idx: int)
    requires
        0 <= idx <= a.len(),
    ensures
        count_rem_prefix(a, r, idx) >= 0,
    decreases idx,
{
    if idx <= 0 {
    } else {
        lemma_count_prefix_nonneg(a, r, idx - 1);
        lemma_count_prefix_split(a, r, idx);
    }
}

proof fn lemma_count_sum_eq_len(a: Seq<i32>, idx: int)
    requires
        0 <= idx <= a.len(),
        forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] >= 0,
    ensures
        count_rem_prefix(a, 0, idx) + count_rem_prefix(a, 1, idx) + count_rem_prefix(a, 2, idx)
            == idx,
    decreases idx,
{
    if idx <= 0 {
    } else {
        lemma_count_sum_eq_len(a, idx - 1);
        lemma_count_prefix_split(a, 0, idx);
        lemma_count_prefix_split(a, 1, idx);
        lemma_count_prefix_split(a, 2, idx);
        lemma_i32_rem3_nonneg(a[idx - 1]);
        let t = rem3(a[idx - 1]);
        assert(t == 0 || t == 1 || t == 2);
        if t == 0 {
            assert(count_rem_prefix(a, 0, idx) == count_rem_prefix(a, 0, idx - 1) + 1);
            assert(count_rem_prefix(a, 1, idx) == count_rem_prefix(a, 1, idx - 1));
            assert(count_rem_prefix(a, 2, idx) == count_rem_prefix(a, 2, idx - 1));
        } else if t == 1 {
            assert(count_rem_prefix(a, 0, idx) == count_rem_prefix(a, 0, idx - 1));
            assert(count_rem_prefix(a, 1, idx) == count_rem_prefix(a, 1, idx - 1) + 1);
            assert(count_rem_prefix(a, 2, idx) == count_rem_prefix(a, 2, idx - 1));
        } else {
            assert(t == 2);
            assert(count_rem_prefix(a, 0, idx) == count_rem_prefix(a, 0, idx - 1));
            assert(count_rem_prefix(a, 1, idx) == count_rem_prefix(a, 1, idx - 1));
            assert(count_rem_prefix(a, 2, idx) == count_rem_prefix(a, 2, idx - 1) + 1);
        }
    }
}

proof fn lemma_min_balance_ops_f_nonneg(c0: int, c1: int, c2: int, tgt: int, fuel: nat)
    requires
        c0 + c1 + c2 == 3 * tgt,
    ensures
        min_balance_ops_f(c0, c1, c2, tgt, fuel) >= 0,
    decreases fuel,
{
    if c0 == tgt && c1 == tgt && c2 == tgt {
    } else if fuel == 0 {
    } else if c0 > tgt {
        lemma_min_balance_ops_f_nonneg(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat);
    } else if c1 > tgt {
        lemma_min_balance_ops_f_nonneg(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat);
    } else {
        assert(c2 > tgt) by {
            assert(c0 + c1 + c2 == 3 * tgt);
            if c2 <= tgt {
                assert(c0 <= tgt);
                assert(c1 <= tgt);
                assert(c2 <= tgt);
                assert(c0 + c1 + c2 <= 3 * tgt);
                assert(c0 + c1 + c2 == 3 * tgt);
                assert(c0 == tgt && c1 == tgt && c2 == tgt);
                assert(false);
            }
        };
        lemma_min_balance_ops_f_nonneg(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat);
    }
}

proof fn lemma_min_balance_result_le_fuel(c0: int, c1: int, c2: int, tgt: int, fuel: nat)
    requires
        c0 + c1 + c2 == 3 * tgt,
    ensures
        min_balance_ops_f(c0, c1, c2, tgt, fuel) <= fuel as int,
    decreases fuel,
{
    if c0 == tgt && c1 == tgt && c2 == tgt {
        assert(min_balance_ops_f(c0, c1, c2, tgt, fuel) == 0);
        assert(0 <= fuel as int);
    } else if fuel == 0 {
        assert(min_balance_ops_f(c0, c1, c2, tgt, fuel) == 0);
    } else {
        assert(fuel > 0);
        if c0 > tgt {
            lemma_min_balance_result_le_fuel(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat);
            assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
                == 1 + min_balance_ops_f(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat));
            assert(min_balance_ops_f(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat) <= (fuel - 1) as int);
            assert(1 + (fuel - 1) as int == fuel as int);
        } else if c1 > tgt {
            lemma_min_balance_result_le_fuel(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat);
            assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
                == 1 + min_balance_ops_f(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat));
            assert(min_balance_ops_f(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat) <= (fuel - 1) as int);
            assert(1 + (fuel - 1) as int == fuel as int);
        } else {
            assert(c2 > tgt) by {
                assert(c0 + c1 + c2 == 3 * tgt);
                if c2 <= tgt {
                    assert(c0 <= tgt);
                    assert(c1 <= tgt);
                    assert(c2 <= tgt);
                    assert(c0 + c1 + c2 <= 3 * tgt);
                    assert(c0 + c1 + c2 == 3 * tgt);
                    assert(c0 == tgt && c1 == tgt && c2 == tgt);
                    assert(false);
                }
            };
            lemma_min_balance_result_le_fuel(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat);
            assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
                == 1 + min_balance_ops_f(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat));
            assert(min_balance_ops_f(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat) <= (fuel - 1) as int);
            assert(1 + (fuel - 1) as int == fuel as int);
        }
    }
}

proof fn lemma_min_balance_unfold_step(c0: int, c1: int, c2: int, tgt: int, fuel: nat)
    requires
        c0 + c1 + c2 == 3 * tgt,
        !(c0 == tgt && c1 == tgt && c2 == tgt),
        fuel > 0,
    ensures
        c0 > tgt ==> min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat),
        (!(c0 > tgt) && c1 > tgt) ==> min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat),
        (!(c0 > tgt) && !(c1 > tgt)) ==> min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat),
{
    assert(!(c0 == tgt && c1 == tgt && c2 == tgt));
    assert(fuel > 0);
    if c0 > tgt {
        assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat));
    } else if c1 > tgt {
        assert(!(c0 > tgt));
        assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat));
    } else {
        assert(!(c0 > tgt));
        assert(!(c1 > tgt));
        assert(c2 > tgt) by {
            assert(c0 + c1 + c2 == 3 * tgt);
            if c2 <= tgt {
                assert(c0 <= tgt);
                assert(c1 <= tgt);
                assert(c2 <= tgt);
                assert(c0 + c1 + c2 <= 3 * tgt);
                assert(c0 + c1 + c2 == 3 * tgt);
                assert(c0 == tgt && c1 == tgt && c2 == tgt);
                assert(false);
            }
        };
        assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat));
    }
}

proof fn lemma_min_balance_pos_unbalanced(c0: int, c1: int, c2: int, tgt: int, fuel: nat)
    requires
        c0 + c1 + c2 == 3 * tgt,
        !(c0 == tgt && c1 == tgt && c2 == tgt),
        fuel > 0,
    ensures
        min_balance_ops_f(c0, c1, c2, tgt, fuel) >= 1,
{
    lemma_min_balance_unfold_step(c0, c1, c2, tgt, fuel);
    if c0 > tgt {
        assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat));
        lemma_min_balance_ops_f_nonneg(c0 - 1, c1 + 1, c2, tgt, (fuel - 1) as nat);
    } else if c1 > tgt {
        assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat));
        lemma_min_balance_ops_f_nonneg(c0, c1 - 1, c2 + 1, tgt, (fuel - 1) as nat);
    } else {
        assert(min_balance_ops_f(c0, c1, c2, tgt, fuel)
            == 1 + min_balance_ops_f(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat));
        lemma_min_balance_ops_f_nonneg(c0 + 1, c1, c2 - 1, tgt, (fuel - 1) as nat);
    }
}


proof fn lemma_min_balance_zero_fuel(c0: int, c1: int, c2: int, tgt: int)
    requires
        c0 + c1 + c2 == 3 * tgt,
    ensures
        min_balance_ops_f(c0, c1, c2, tgt, 0nat) == 0,
{
    
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn min_moves_balance_remainders(a: Vec<i32>) -> (result: i32)
        requires
            3 <= a.len() && a.len() <= 30_000,
            a.len() % 3 == 0,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 100,
        ensures
            result == min_balance_ops_f(
                count_rem(a@, 0),
                count_rem(a@, 1),
                count_rem(a@, 2),
                (a.len() / 3) as int,
                (a.len() * 3) as nat,
            ),
    {
        let n = a.len();
        let tgt = n / 3;
        let mut c0: usize = 0;
        let mut c1: usize = 0;
        let mut c2: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                3 <= n && n <= 30_000,
                n % 3 == 0,
                forall|j: int| 0 <= j < a.len() ==> 0 <= #[trigger] a[j] <= 100,
                i <= n,
                c0 + c1 + c2 == i,
                c0 as int == count_rem_prefix(a@, 0, i as int),
                c1 as int == count_rem_prefix(a@, 1, i as int),
                c2 as int == count_rem_prefix(a@, 2, i as int),
            decreases n - i,
        {
            proof {
                lemma_i32_rem3_nonneg(a[i as int]);
            }
            let r = a[i] % 3;
            proof {
                lemma_i32_rem3_nonneg(a[i as int]);
                assert((a[i as int] % 3) as int == rem3(a[i as int]));
            }
            if r == 0 {
                c0 = c0 + 1;
            } else if r == 1 {
                c1 = c1 + 1;
            } else {
                c2 = c2 + 1;
            }
            proof {
                lemma_count_prefix_split(a@, 0, i + 1);
                lemma_count_prefix_split(a@, 1, i + 1);
                lemma_count_prefix_split(a@, 2, i + 1);
                lemma_i32_rem3_nonneg(a[i as int]);
                if r == 0 {
                    assert(count_rem_prefix(a@, 0, (i + 1) as int) == count_rem_prefix(a@, 0, i as int) + 1);
                    assert(count_rem_prefix(a@, 1, (i + 1) as int) == count_rem_prefix(a@, 1, i as int));
                    assert(count_rem_prefix(a@, 2, (i + 1) as int) == count_rem_prefix(a@, 2, i as int));
                } else if r == 1 {
                    assert(count_rem_prefix(a@, 0, (i + 1) as int) == count_rem_prefix(a@, 0, i as int));
                    assert(count_rem_prefix(a@, 1, (i + 1) as int) == count_rem_prefix(a@, 1, i as int) + 1);
                    assert(count_rem_prefix(a@, 2, (i + 1) as int) == count_rem_prefix(a@, 2, i as int));
                } else {
                    assert(count_rem_prefix(a@, 0, (i + 1) as int) == count_rem_prefix(a@, 0, i as int));
                    assert(count_rem_prefix(a@, 1, (i + 1) as int) == count_rem_prefix(a@, 1, i as int));
                    assert(count_rem_prefix(a@, 2, (i + 1) as int) == count_rem_prefix(a@, 2, i as int) + 1);
                }
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(c0 as int == count_rem(a@, 0));
            assert(c1 as int == count_rem(a@, 1));
            assert(c2 as int == count_rem(a@, 2));
            assert(forall|j: int| 0 <= j < a.len() ==> a@[j] >= 0);
            lemma_count_sum_eq_len(a@, n as int);
            assert(c0 as int + c1 as int + c2 as int == n as int);
            assert((tgt as int) * 3 == n as int);
        }
        let ghost ic0 = c0 as int;
        let ghost ic1 = c1 as int;
        let ghost ic2 = c2 as int;
        let ghost itgt = tgt as int;
        proof {
            assert(ic0 + ic1 + ic2 == n as int);
            assert(itgt == tgt as int);
            assert(3 * itgt == n as int);
            assert(ic0 + ic1 + ic2 == 3 * itgt);
        }
        let ghost init_val = min_balance_ops_f(ic0, ic1, ic2, itgt, (n * 3) as nat);
        proof {
            assert(ic0 + ic1 + ic2 == 3 * itgt);
            lemma_min_balance_result_le_fuel(ic0, ic1, ic2, itgt, (n * 3) as nat);
            assert(init_val <= 3 * (n as int));
            lemma_min_balance_ops_f_nonneg(ic0, ic1, ic2, itgt, (n * 3) as nat);
            assert(init_val >= 0);
        }
        let mut ops: usize = 0;
        let total3: usize = n * 3;
        proof {
            assert(ops == 0);
            assert((ops as int) <= init_val);
            assert(total3 == n * 3);
        }
        #[verifier::loop_isolation(false)]
        while (c0 != tgt || c1 != tgt || c2 != tgt) && ops < total3
            invariant
                n == a.len(),
                n <= 30000,
                tgt == n / 3,
                total3 == n * 3,
                c0 + c1 + c2 == n,
                c0 as int + c1 as int + c2 as int == 3 * itgt,
                ic0 + ic1 + ic2 == 3 * itgt,
                ic0 == count_rem(a@, 0),
                ic1 == count_rem(a@, 1),
                ic2 == count_rem(a@, 2),
                itgt == (n / 3) as int,
                init_val <= 3 * (n as int),
                init_val == min_balance_ops_f(ic0, ic1, ic2, itgt, (n * 3) as nat),
                ops <= total3,
                ops as int
                    + min_balance_ops_f(
                        c0 as int,
                        c1 as int,
                        c2 as int,
                        itgt,
                        (n * 3 - ops) as nat,
                    ) == init_val,
                ops as int <= init_val,
            decreases total3 - ops,
        {
            proof {
                assert(c0 as int + c1 as int + c2 as int == 3 * itgt);
                assert(!(c0 as int == itgt && c1 as int == itgt && c2 as int == itgt));
                assert(ops < total3);
                assert(n * 3 - ops > 0);
                assert((n * 3 - ops) as nat > 0);
                assert((ops as int) <= init_val);
                assert(init_val == ops as int + min_balance_ops_f(
                    c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                ));
                assert(init_val <= 3 * (n as int));
                lemma_min_balance_ops_f_nonneg(
                    c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                );
                assert((ops as int) <= init_val);
                lemma_min_balance_pos_unbalanced(
                    c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                );
                lemma_min_balance_unfold_step(
                    c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                );
            }
            if c0 > tgt {
                let ghost old_c0 = c0 as int;
                let ghost old_c1 = c1 as int;
                let ghost old_c2 = c2 as int;
                let ghost old_ops = ops;
                let ghost old_fuel = (n * 3 - ops) as nat;
                c0 = c0 - 1;
                c1 = c1 + 1;
                proof {
                    assert(ops < n * 3);
                    assert(ops + 1 <= n * 3);
                }
                ops = ops + 1;
                proof {
                    assert(old_c0 > itgt);
                    lemma_min_balance_unfold_step(old_c0, old_c1, old_c2, itgt, old_fuel);
                    assert(min_balance_ops_f(old_c0, old_c1, old_c2, itgt, old_fuel)
                        == 1 + min_balance_ops_f(
                            c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                        ));
                    assert(init_val == old_ops as int + min_balance_ops_f(
                        old_c0, old_c1, old_c2, itgt, old_fuel,
                    ));
                    assert(init_val == ops as int + min_balance_ops_f(
                        c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                    ));
                    lemma_min_balance_ops_f_nonneg(
                        c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                    );
                }
            } else if c1 > tgt {
                let ghost old_c0 = c0 as int;
                let ghost old_c1 = c1 as int;
                let ghost old_c2 = c2 as int;
                let ghost old_ops = ops;
                let ghost old_fuel = (n * 3 - ops) as nat;
                c1 = c1 - 1;
                c2 = c2 + 1;
                proof {
                    assert(ops < n * 3);
                    assert(ops + 1 <= n * 3);
                }
                ops = ops + 1;
                proof {
                    assert(!(old_c0 > itgt));
                    assert(old_c1 > itgt);
                    lemma_min_balance_unfold_step(old_c0, old_c1, old_c2, itgt, old_fuel);
                    assert(min_balance_ops_f(old_c0, old_c1, old_c2, itgt, old_fuel)
                        == 1 + min_balance_ops_f(
                            c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                        ));
                    assert(init_val == old_ops as int + min_balance_ops_f(
                        old_c0, old_c1, old_c2, itgt, old_fuel,
                    ));
                    assert(init_val == ops as int + min_balance_ops_f(
                        c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                    ));
                    lemma_min_balance_ops_f_nonneg(
                        c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                    );
                }
            } else {
                let ghost old_c0 = c0 as int;
                let ghost old_c1 = c1 as int;
                let ghost old_c2 = c2 as int;
                let ghost old_ops = ops;
                let ghost old_fuel = (n * 3 - ops) as nat;
                c2 = c2 - 1;
                c0 = c0 + 1;
                proof {
                    assert(ops < n * 3);
                    assert(ops + 1 <= n * 3);
                }
                ops = ops + 1;
                proof {
                    assert(!(old_c0 > itgt));
                    assert(!(old_c1 > itgt));
                    lemma_min_balance_unfold_step(old_c0, old_c1, old_c2, itgt, old_fuel);
                    assert(min_balance_ops_f(old_c0, old_c1, old_c2, itgt, old_fuel)
                        == 1 + min_balance_ops_f(
                            c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                        ));
                    assert(init_val == old_ops as int + min_balance_ops_f(
                        old_c0, old_c1, old_c2, itgt, old_fuel,
                    ));
                    assert(init_val == ops as int + min_balance_ops_f(
                        c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                    ));
                    lemma_min_balance_ops_f_nonneg(
                        c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat,
                    );
                }
            }
        }
        proof {
            
            
            if c0 == tgt && c1 == tgt && c2 == tgt {
                
                assert(min_balance_ops_f(c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat) == 0);
            } else {
                
                assert(ops == total3);
                assert(n * 3 - ops == 0);
                lemma_min_balance_zero_fuel(c0 as int, c1 as int, c2 as int, itgt);
                assert(min_balance_ops_f(c0 as int, c1 as int, c2 as int, itgt, (n * 3 - ops) as nat) == 0);
            }
            assert(init_val == ops as int);
        }
        ops as i32
    }
}

}