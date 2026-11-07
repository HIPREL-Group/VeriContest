use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn capped_trips_prefix(time: Seq<i32>, t: int, cap: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            let prev = Self::capped_trips_prefix(time, t, cap, n - 1);
            let s = prev + t / (time[n - 1] as int);
            if s >= cap { cap } else { s }
        }
    }

    pub open spec fn feasible(time: Seq<i32>, t: int, total: int) -> bool {
        Self::capped_trips_prefix(time, t, total, time.len() as int) == total
    }

    proof fn lemma_div_time_monotonic(d: int, t1: int, t2: int)
        requires
            1 <= d,
            0 <= t1 <= t2,
        ensures
            t1 / d <= t2 / d,
    {
        assert((t1 / d) <= (t2 / d)) by (nonlinear_arith)
            requires 1 <= d, 0 <= t1 <= t2
        {
        }
    }

    proof fn lemma_capped_trips_time_monotonic(time: Seq<i32>, t1: int, t2: int, cap: int, n: int)
        requires
            0 <= n <= time.len(),
            0 <= t1 <= t2,
            1 <= cap,
            forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
        ensures
            Self::capped_trips_prefix(time, t1, cap, n) <= Self::capped_trips_prefix(time, t2, cap, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_capped_trips_time_monotonic(time, t1, t2, cap, n - 1);
            assert(1 <= time[n - 1] as int);
            Self::lemma_div_time_monotonic(time[n - 1] as int, t1, t2);
            let p1 = Self::capped_trips_prefix(time, t1, cap, n - 1);
            let p2 = Self::capped_trips_prefix(time, t2, cap, n - 1);
            let s1 = p1 + t1 / (time[n - 1] as int);
            let s2 = p2 + t2 / (time[n - 1] as int);
            assert(p1 + t1 / (time[n - 1] as int) <= p2 + t1 / (time[n - 1] as int)) by (nonlinear_arith)
                requires p1 <= p2
            {
            }
            assert(p2 + t1 / (time[n - 1] as int) <= p2 + t2 / (time[n - 1] as int)) by (nonlinear_arith)
                requires t1 / (time[n - 1] as int) <= t2 / (time[n - 1] as int)
            {
            }
            assert(s1 == p1 + t1 / (time[n - 1] as int));
            assert(s2 == p2 + t2 / (time[n - 1] as int));
            let m = p2 + t1 / (time[n - 1] as int);
            assert(s1 <= m);
            assert(m <= s2);
            assert(s1 <= s2);
            assert(Self::capped_trips_prefix(time, t1, cap, n) == if s1 >= cap { cap } else { s1 });
            assert(Self::capped_trips_prefix(time, t2, cap, n) == if s2 >= cap { cap } else { s2 });
            assert((if s1 >= cap { cap } else { s1 }) <= (if s2 >= cap { cap } else { s2 })) by (nonlinear_arith)
                requires s1 <= s2
            {
            }
        }
    }

    proof fn lemma_feasible_time_monotonic(time: Seq<i32>, t1: int, t2: int, total: int)
        requires
            0 <= t1 <= t2,
            1 <= total,
            Self::feasible(time, t1, total),
            forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
        ensures
            Self::feasible(time, t2, total),
    {
        Self::lemma_capped_trips_time_monotonic(time, t1, t2, total, time.len() as int);
    }

    proof fn lemma_capped_sticky(time: Seq<i32>, t: int, cap: int, n: int)
        requires
            1 <= cap,
            0 <= t,
            1 <= n < time.len(),
            forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
            Self::capped_trips_prefix(time, t, cap, n) == cap,
        ensures
            Self::capped_trips_prefix(time, t, cap, n + 1) == cap,
    {
        reveal_with_fuel(Solution::capped_trips_prefix, 2);
        let prev = Self::capped_trips_prefix(time, t, cap, n);
        let s = prev + t / (time[n] as int);
        assert(prev == cap);
        assert(1 <= time[n] as int);
        assert(0 <= t / (time[n] as int)) by (nonlinear_arith)
            requires 0 <= t, 1 <= time[n] as int
        {
        }
        assert(s == cap + t / (time[n] as int));
        assert(s >= cap) by (nonlinear_arith)
            requires s == cap + t / (time[n] as int), 0 <= t / (time[n] as int)
        {
        }
        assert(Self::capped_trips_prefix(time, t, cap, n + 1) == cap);
    }

    proof fn lemma_capped_from_one_full(time: Seq<i32>, t: int, cap: int, n: int)
        requires
            1 <= n <= time.len(),
            0 <= t,
            1 <= cap,
            forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
            Self::capped_trips_prefix(time, t, cap, 1) == cap,
        ensures
            Self::capped_trips_prefix(time, t, cap, n) == cap,
        decreases n,
    {
        if n > 1 {
            Self::lemma_capped_from_one_full(time, t, cap, n - 1);
            Self::lemma_capped_sticky(time, t, cap, n - 1);
        }
    }

    proof fn lemma_feasible_at_upper_bound(time: Seq<i32>, total: int)
        requires
            1 <= time.len() <= 100000,
            1 <= total <= 10000000,
            forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
        ensures
            Self::feasible(time, 100000000000000, total),
    {
        reveal_with_fuel(Solution::capped_trips_prefix, 2);
        assert(1 <= time[0] as int <= 10000000);
        assert(100000000000000int / (time[0] as int) >= 10000000) by (nonlinear_arith)
            requires 1 <= time[0] as int <= 10000000
        {
        }
        assert(10000000 >= total) by (nonlinear_arith)
            requires total <= 10000000
        {
        }
        assert(100000000000000int / (time[0] as int) >= total) by (nonlinear_arith)
            requires 100000000000000int / (time[0] as int) >= 10000000, 10000000 >= total
        {
        }
        assert(Self::capped_trips_prefix(time, 100000000000000int, total, 0) == 0);
        assert(Self::capped_trips_prefix(time, 100000000000000int, total, 1) == total);
        Self::lemma_capped_from_one_full(time, 100000000000000int, total, time.len() as int);
        assert(Self::capped_trips_prefix(time, 100000000000000int, total, time.len() as int) == total);
    }

    fn can_finish(time: &Vec<i32>, t: i64, total: i32) -> (ok: bool)
        requires
            1 <= time.len() <= 100000,
            forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
            1 <= t <= 100000000000000,
            1 <= total <= 10000000,
        ensures
            ok == Self::feasible(time@, t as int, total as int),
    {
        let mut trips: i64 = 0;
        let target = total as i64;
        let mut i: usize = 0;
        while i < time.len()
            invariant
                0 <= i <= time.len(),
                1 <= t <= 100000000000000,
                1 <= target <= 10000000,
                1 <= time.len() <= 100000,
                forall |j: int| 0 <= j < time.len() ==> 1 <= #[trigger] time[j] <= 10000000,
                trips as int == Self::capped_trips_prefix(time@, t as int, target as int, i as int),
                0 <= trips <= target,
            decreases time.len() - i,
        {
            let add = t / (time[i] as i64);
            if trips >= target - add {
                trips = target;
            } else {
                trips = trips + add;
            }
            i = i + 1;
        }
        trips == target
    }

    pub fn minimum_time(time: Vec<i32>, total_trips: i32) -> (ans: i64)
        requires
            1 <= time.len() <= 100000,
            forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
            1 <= total_trips <= 10000000,
        ensures
            1 <= ans <= 100000000000000,
            Self::feasible(time@, ans as int, total_trips as int),
            forall |t: int| 1 <= t < ans ==> !#[trigger] Self::feasible(time@, t, total_trips as int),
    {
        proof {
            Self::lemma_feasible_at_upper_bound(time@, total_trips as int);
        }

        let mut left: i64 = 1;
        let mut right: i64 = 100000000000000;
        while left < right
            invariant
                1 <= left <= right <= 100000000000000,
                1 <= total_trips <= 10000000,
                1 <= time.len() <= 100000,
                Self::feasible(time@, right as int, total_trips as int),
                forall |d: int| 1 <= d < left ==> !#[trigger] Self::feasible(time@, d, total_trips as int),
                forall |i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            if Self::can_finish(&time, mid, total_trips) {
                right = mid;
            } else {
                proof {
                    assert(!Self::feasible(time@, mid as int, total_trips as int));
                    assert forall |d: int| 1 <= d < mid + 1 implies !Self::feasible(time@, d, total_trips as int) by {
                        if d < left {
                        } else {
                            assert(left <= d <= mid);
                            if Self::feasible(time@, d, total_trips as int) {
                                Self::lemma_feasible_time_monotonic(time@, d, mid as int, total_trips as int);
                                assert(Self::feasible(time@, mid as int, total_trips as int));
                            }
                        }
                    }
                }
                left = mid + 1;
            }
        }
        left
    }
}

}
