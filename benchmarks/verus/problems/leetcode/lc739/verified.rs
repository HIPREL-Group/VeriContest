use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn bounded_temps(temps: Seq<i32>) -> bool {
    forall |i: int| 0 <= i < temps.len() ==> 30 <= #[trigger] temps[i] <= 100
}

pub open spec fn correct_at(temps: Seq<i32>, res: Seq<i32>, k: int) -> bool {
    0 <= k < temps.len()
    && 0 <= res[k]
    && res[k] <= temps.len() - 1 - k
    && if res[k] == 0 {
        forall |m: int| k < m < temps.len() ==> temps[m] <= temps[k]
    } else {
        let d = res[k] as int;
        1 <= d && k + d < temps.len()
        && temps[k + d] > temps[k]
        && forall |m: int| k < m < k + d ==> temps[m] <= temps[k]
    }
}

pub open spec fn next_pos_ok_for(temps: Seq<i32>, start: int, next: Seq<usize>, t: int) -> bool {
    0 <= t < next.len()
    && start <= (next[t] as int)
    && (next[t] as int) <= temps.len()
    && (if (next[t] as int) < temps.len() {
        temps[next[t] as int] == t as i32
        && forall |m: int| start <= m < (next[t] as int) ==> temps[m] != t as i32
    } else {
        forall |m: int| start <= m < temps.len() ==> temps[m] != t as i32
    })
}

pub proof fn i32_cast_nonneg(x: int)
    requires
        0 <= x <= 100_000,
    ensures
        0 <= (x as i32),
        ((x as i32) as int) == x,
{
    assert(x < 0x8000_0000) by (nonlinear_arith)
        requires
            x <= 100_000,
    {}
    assert(0 <= (x as i32));
    assert(((x as i32) as int) == x);
}

pub proof fn no_warmer_after(temps: Seq<i32>, next: Seq<usize>, idx: int)
    requires
        bounded_temps(temps),
        0 <= idx < temps.len(),
        next.len() == 101,
        forall |t: int| 0 <= t <= 100 ==> #[trigger] next_pos_ok_for(temps, idx + 1, next, t),
        forall |t: int| temps[idx] < t <= 100 ==> next[t] as int == temps.len(),
    ensures
        forall |m: int| idx < m < temps.len() ==> temps[m] <= temps[idx]
{
    assert forall |m: int| idx < m < temps.len() implies temps[m] <= temps[idx] by {
        if temps[m] > temps[idx] {
            assert(30 <= temps[m] <= 100);
            let t = temps[m] as int;
            assert(t as i32 == temps[m]);
            assert(temps[idx] < t <= 100);
            assert(next[t] as int == temps.len());
            assert(next_pos_ok_for(temps, idx + 1, next, t));
            assert(temps[m] != t as i32);
        }
    }
}

pub proof fn warmer_after_at_best(temps: Seq<i32>, next: Seq<usize>, idx: int, best: int)
    requires
        bounded_temps(temps),
        0 <= idx < best < temps.len(),
        next.len() == 101,
        forall |t: int| 0 <= t <= 100 ==> #[trigger] next_pos_ok_for(temps, idx + 1, next, t),
        exists |t: int| temps[idx] < t <= 100 && next[t] as int == best,
        forall |t: int| temps[idx] < t <= 100 ==> best <= next[t] as int,
    ensures
        temps[best] > temps[idx],
        forall |m: int| idx < m < best ==> temps[m] <= temps[idx]
{
    let witness = choose |t: int| temps[idx] < t <= 100 && next[t] as int == best;
    assert(next_pos_ok_for(temps, idx + 1, next, witness));
    assert(temps[best] == witness as i32);
    assert((temps[idx] as int) < witness);
    assert(temps[idx] < witness as i32);
    assert(temps[best] > temps[idx]);
    assert forall |m: int| idx < m < best implies temps[m] <= temps[idx] by {
        if temps[m] > temps[idx] {
            assert(30 <= temps[m] <= 100);
            let t = temps[m] as int;
            assert(t as i32 == temps[m]);
            assert(temps[idx] < t <= 100);
            assert(next_pos_ok_for(temps, idx + 1, next, t));
            if next[t] as int == temps.len() {
                assert(temps[m] != t as i32);
            } else {
                if m < next[t] as int {
                    assert(temps[m] != t as i32);
                }
            }
            assert((next[t] as int) <= m);
            assert(best <= next[t] as int);
            assert(best <= m);
        }
    }
}

pub proof fn correct_at_preserved_update(temps: Seq<i32>, res: Seq<i32>, i: int, k: int, v: i32)
    requires
        0 <= i < temps.len(),
        0 <= k < temps.len(),
        i != k,
        correct_at(temps, res, k),
        res.len() == temps.len(),
    ensures
        correct_at(temps, res.update(i, v), k),
{
    assert(res.update(i, v)[k] == res[k]);
}

impl Solution {
    pub fn daily_temperatures(temperatures: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= temperatures.len() <= 100_000,
            forall |i: int| 0 <= i < temperatures.len() ==> 30 <= #[trigger] temperatures[i] <= 100,
        ensures
            res.len() == temperatures.len(),
            forall |i: int| 0 <= i < temperatures.len() ==>
                0 <= #[trigger] res[i] && res[i] as int <= temperatures.len() - 1 - i
                && if res[i] == 0 {
                    forall |j: int| i < j < temperatures.len() ==> temperatures[j] <= temperatures[i]
                } else {
                    let d = res[i] as int;
                    1 <= d && i + d < temperatures.len()
                    && temperatures[i + d] > temperatures[i]
                    && forall |j: int| i < j < i + d ==> temperatures[j] <= temperatures[i]
                },
    {
        let n = temperatures.len();
        let ghost n_int: int = n as int;
        proof {
            assert(n_int == n as int);
            assert(n_int <= 100_000);
            assert(temperatures@.len() as int == n_int);
            assert(bounded_temps(temperatures@));
        }

        let mut res: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                0 <= idx <= n,
                res.len() == idx,
                res@.len() as int == idx as int,
                n == temperatures.len(),
                n_int == n as int,
                n <= 100_000,
                forall |k: int| 0 <= k < idx as int ==> res@[k] == 0,
            decreases n - idx
        {
            res.push(0);
            idx = idx + 1;
        }

        proof {
            assert(res@.len() as int == n_int);
            assert(forall |k: int| #![trigger res@[k]] 0 <= k < n_int ==> res@[k] == 0);
        }

        let mut next_pos: Vec<usize> = Vec::new();
        let mut t0: usize = 0;
        while t0 <= 100
            invariant
                0 <= t0 <= 101,
                next_pos.len() == t0,
                forall |t: int| 0 <= t < t0 as int ==> next_pos@[t] == n,
            decreases 101 - t0
        {
            next_pos.push(n);
            t0 = t0 + 1;
        }

        proof {
            assert(next_pos@.len() == 101);
            assert(forall |t: int| 0 <= t <= 100 ==> next_pos@[t] == n);
            assert forall |t: int| 0 <= t <= 100 implies #[trigger] next_pos_ok_for(temperatures@, n_int, next_pos@, t) by {
                assert(next_pos@[t] as int == n_int);
            }
        }

        let mut i: usize = n;
        while i > 0
            invariant
                0 <= i <= n,
                n == temperatures.len(),
                n_int == n as int,
                n <= 100_000,
                bounded_temps(temperatures@),
                res@.len() as int == n_int,
                next_pos@.len() == 101,
                forall |k: int| 0 <= k < i as int ==> res@[k] == 0,
                forall |k: int| 0 <= k < n_int ==> 0 <= res@[k],
                forall |k: int| #![trigger correct_at(temperatures@, res@, k)] i as int <= k < n_int ==> correct_at(temperatures@, res@, k),
                forall |t: int| 0 <= t <= 100 ==> #[trigger] next_pos_ok_for(temperatures@, i as int, next_pos@, t),
            decreases i
        {
            let idx = i - 1;
            let ghost res_before = res@;
            proof {
                assert(0 <= idx < n);
                assert(30 <= temperatures@[idx as int] <= 100);
            }
            let ghost next_before = next_pos@;
            let cur = temperatures[idx] as usize;
            let mut best: usize = n;
            let mut t: usize = cur + 1;
            while t <= 100
                invariant
                    next_pos.len() == 101,
                    next_pos@ == next_before,
                    next_before.len() == 101,
                    0 <= idx < n,
                    (cur as int) == (temperatures@[idx as int] as int),
                    cur <= 100,
                    cur + 1 <= t <= 101,
                    best <= n,
                    forall |temp: int| 0 <= temp <= 100 ==> #[trigger] next_pos_ok_for(temperatures@, i as int, next_before, temp),
                    forall |q: int| ((cur as int) < q && q < (t as int)) ==> (best as int) <= (next_before[q] as int),
                    best < n ==> exists |q: int| ((cur as int) < q && q < (t as int)) && (best as int) == (next_before[q] as int),
                decreases 101 - t
            {
                let ghost t_old: int = t as int;
                let ghost best_old: int = best as int;
                let candidate = next_pos[t];
                if candidate < best {
                    best = candidate;
                }
                t = t + 1;
                proof {
                    assert((cur as int) < t_old && t_old <= 100);
                    assert((candidate as int) == (next_before[t_old] as int));
                    assert forall |q: int| ((cur as int) < q && q < (t as int)) implies (best as int) <= (next_before[q] as int) by {
                        if q == t_old {
                            if candidate < best_old as usize {
                                assert((best as int) == (candidate as int));
                            } else {
                                assert((best as int) == best_old);
                                assert(best_old <= (candidate as int));
                            }
                        } else {
                            assert((cur as int) < q && q < t_old);
                            if candidate < best_old as usize {
                                assert((best as int) == (candidate as int));
                                assert((candidate as int) < best_old);
                                assert(best_old <= (next_before[q] as int));
                            } else {
                                assert((best as int) == best_old);
                            }
                        }
                    }
                    if best < n {
                        if candidate < best_old as usize {
                            assert((best as int) == (candidate as int));
                            assert((cur as int) < t_old && t_old < (t as int));
                            assert((best as int) == (next_before[t_old] as int));
                        } else {
                            assert((best as int) == best_old);
                        }
                    }
                }
            }

            if best < n {
                proof {
                    let witness = choose |q: int| ((cur as int) < q && q < 101) && (best as int) == (next_before[q] as int);
                    assert(next_pos_ok_for(temperatures@, i as int, next_before, witness));
                    assert(i as int <= best as int);
                    assert(idx < best);
                }
                let d: i32 = (best - idx) as i32;
                proof {
                    assert(exists |q: int| ((cur as int) < q && q < 101) && (best as int) == (next_before[q] as int));
                    warmer_after_at_best(temperatures@, next_before, idx as int, best as int);
                    assert(0 <= (best as int) - (idx as int));
                    assert((best as int) - (idx as int) < n_int) by (nonlinear_arith)
                        requires
                            idx < best,
                            best < n,
                            n_int == n as int,
                    {}
                    assert((best as int) - (idx as int) <= 100_000) by (nonlinear_arith)
                        requires
                            (best as int) - (idx as int) < n_int,
                            n_int <= 100_000,
                    {}
                    i32_cast_nonneg((best as int) - (idx as int));
                    assert(d == ((best as int) - (idx as int)) as i32);
                    assert((d as int) == (best as int) - (idx as int));
                    assert(1 <= (d as int) && (idx as int) + (d as int) < temperatures.len());
                    assert(temperatures@[(idx as int) + (d as int)] == temperatures@[best as int]);
                    assert(correct_at(temperatures@, res_before.update(idx as int, d), idx as int));
                }
                res[idx] = d;
            } else {
                proof {
                    assert forall |q: int| ((cur as int) < q && q < 101) implies (next_before[q] as int) == n_int by {
                        assert((best as int) <= (next_before[q] as int));
                        assert(next_pos_ok_for(temperatures@, i as int, next_before, q));
                        assert((next_before[q] as int) <= n_int);
                    }
                    no_warmer_after(temperatures@, next_before, idx as int);
                    assert(res_before[idx as int] == 0);
                    assert(correct_at(temperatures@, res_before, idx as int));
                }
                res[idx] = 0;
            }

            next_pos[cur] = idx;
            proof {
                assert(next_before.update(cur as int, idx) == next_pos@);
                assert forall |temp: int| 0 <= temp <= 100 implies #[trigger] next_pos_ok_for(temperatures@, idx as int, next_pos@, temp) by {
                    if temp == cur as int {
                        assert(next_pos@[temp] == idx);
                        assert(temperatures@[idx as int] == temp as i32);
                    } else {
                        assert(next_pos@[temp] == next_before[temp]);
                        assert(next_pos_ok_for(temperatures@, idx as int + 1, next_before, temp));
                        assert(temperatures@[idx as int] != temp as i32);
                    }
                }
                assert forall |k: int| idx as int <= k < n_int implies correct_at(temperatures@, res@, k) by {
                    if k == idx as int {
                        if best < n {
                            assert(correct_at(temperatures@, res_before.update(idx as int, res@[idx as int]), idx as int));
                        } else {
                            assert(correct_at(temperatures@, res_before, idx as int));
                            assert(res_before == res@);
                        }
                    } else {
                        assert(idx as int != k);
                        correct_at_preserved_update(
                            temperatures@,
                            res_before,
                            idx as int,
                            k,
                            res@[idx as int],
                        );
                        assert(res_before.update(idx as int, res@[idx as int]) == res@);
                    }
                }
            }
            i = idx;
        }

        proof {
            assert(i == 0);
            assert(forall |k: int| 0 <= k < n_int ==> correct_at(temperatures@, res@, k));
            assert forall |idx: int| 0 <= idx < temperatures.len() implies
                0 <= #[trigger] res[idx] && res[idx] as int <= temperatures.len() - 1 - idx
                && if res[idx] == 0 {
                    forall |j: int| idx < j < temperatures.len() ==> temperatures[j] <= temperatures[idx]
                } else {
                    let d = res[idx] as int;
                    1 <= d && idx + d < temperatures.len()
                    && temperatures[idx + d] > temperatures[idx]
                    && forall |j: int| idx < j < idx + d ==> temperatures[j] <= temperatures[idx]
                } by {
                    assert(correct_at(temperatures@, res@, idx));
                }
        }

        res
    }
}

}
