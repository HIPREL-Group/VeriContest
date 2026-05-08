use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_spec(ts: Seq<i32>, duration: int, i: nat, total: int) -> int
        recommends i <= ts.len(),
        decreases ts.len() - i,
    {
        if i >= ts.len() {
            total
        } else if i + 1 >= ts.len() {
            total + duration
        } else {
            let gap = (ts[(i + 1) as int] as int) - (ts[i as int] as int);
            let contrib = if gap < duration { gap } else { duration };
            Self::scan_spec(ts, duration, i + 1, total + contrib)
        }
    }

    pub open spec fn find_poisoned_duration_spec(ts: Seq<i32>, duration: int) -> int {
        if ts.len() == 0 { 0 } else { Self::scan_spec(ts, duration, 0, 0) }
    }

    pub fn find_poisoned_duration(time_series: Vec<i32>, duration: i32) -> (res: i32)
        requires
            1 <= time_series.len() <= 10_000,
            0 <= duration <= 10_000_000,
            forall |j: int| 0 <= j < time_series@.len() ==> 0 <= #[trigger] time_series@[j] <= 10_000_000i32,
            forall |j: int| 0 <= j < time_series@.len() - 1 ==>
                #[trigger] time_series@[j] <= time_series@[j + 1],
            Self::find_poisoned_duration_spec(time_series@, duration as int) <= i32::MAX as int,
        ensures
            res as int == Self::find_poisoned_duration_spec(time_series@, duration as int),
    {
        let n = time_series.len();
        let mut total: i64 = 0i64;
        let mut i: usize = 0;

        while i < n
            invariant
                n == time_series.len(),
                1 <= n <= 10_000,
                0 <= i <= n,
                0 <= duration <= 10_000_000,
                forall |j: int| 0 <= j < time_series@.len() ==>
                    0 <= #[trigger] time_series@[j] <= 10_000_000i32,
                forall |j: int| 0 <= j < time_series@.len() - 1 ==>
                    #[trigger] time_series@[j] <= time_series@[j + 1],
                Self::find_poisoned_duration_spec(time_series@, duration as int) <= i32::MAX as int,
                total >= 0,
                total as int <= i as int * duration as int,
                Self::scan_spec(time_series@, duration as int, i as nat, total as int)
                    == Self::find_poisoned_duration_spec(time_series@, duration as int),
            decreases n - i,
        {
            let ghost old_i = i as nat;
            let ghost old_total = total as int;
            let ghost ts = time_series@;
            let ghost d = duration as int;

            if i + 1 < n {
                let gap: i64 = time_series[i + 1] as i64 - time_series[i] as i64;
                let contrib: i64 = if gap < duration as i64 { gap } else { duration as i64 };

                proof {
                    assert(gap as int == ts[(i + 1) as int] as int - ts[i as int] as int);
                    assert(0 <= gap);
                    assert(contrib >= 0);
                    assert(contrib as int <= d);

                    assert(contrib as int
                        == if (ts[(old_i + 1) as int] as int - ts[old_i as int] as int) < d {
                            ts[(old_i + 1) as int] as int - ts[old_i as int] as int
                        } else {
                            d
                        });

                    assert(Self::scan_spec(ts, d, old_i, old_total)
                        == Self::scan_spec(ts, d, old_i + 1, old_total + contrib as int));

                    assert(total + contrib <= i64::MAX) by (nonlinear_arith)
                        requires
                            total as int <= i as int * duration as int,
                            contrib as int <= duration as int,
                            0 <= duration as int,
                            duration <= 10_000_000,
                            i < n,
                            n <= 10_000,
                    {}
                }

                total += contrib;

                proof {
                    assert(total as int == old_total + contrib as int);
                    assert(Self::scan_spec(ts, d, old_i + 1, total as int)
                        == Self::find_poisoned_duration_spec(ts, d));
                    assert(total as int <= (i + 1) as int * d) by (nonlinear_arith)
                        requires
                            total as int == old_total + contrib as int,
                            old_total <= i as int * d,
                            contrib as int <= d,
                            0 <= d,
                    {}
                }
            } else {
                proof {
                    assert(i + 1 >= ts.len());
                    assert(old_i + 1 >= ts.len());
                    assert(Self::scan_spec(ts, d, old_i, old_total)
                        == old_total + d);

                    assert(total + duration as i64 <= i64::MAX) by (nonlinear_arith)
                        requires
                            total as int <= i as int * duration as int,
                            i < n,
                            n <= 10_000,
                            duration <= 10_000_000,
                    {}
                }

                total += duration as i64;

                proof {
                    assert(total as int == old_total + d);
                    assert(old_i + 1 >= ts.len());
                    assert(Self::scan_spec(ts, d, (old_i + 1) as nat, total as int) == total as int);
                    assert(Self::scan_spec(ts, d, (old_i + 1) as nat, total as int)
                        == Self::find_poisoned_duration_spec(ts, d));
                    assert(total as int <= (i + 1) as int * d) by (nonlinear_arith)
                        requires
                            total as int == old_total + d,
                            old_total <= i as int * d,
                            0 <= d,
                    {}
                }
            }

            i += 1;
        }

        proof {
            assert(i == n);
            assert(Self::scan_spec(time_series@, duration as int, n as nat, total as int)
                == Self::find_poisoned_duration_spec(time_series@, duration as int));
            assert(n as nat >= time_series@.len());
            assert(Self::scan_spec(time_series@, duration as int, n as nat, total as int) == total as int);
            assert(total as int == Self::find_poisoned_duration_spec(time_series@, duration as int));
            assert(total as int <= i32::MAX as int);
        }

        total as i32
    }
}

} 
