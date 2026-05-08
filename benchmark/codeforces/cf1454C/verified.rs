use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_x_segments(a: Seq<i64>, x: int, end: int) -> nat
        recommends
            0 <= end <= a.len(),
        decreases end,
    {
        if end <= 0 {
            0nat
        } else if a[end - 1] as int == x {
            if end >= 2 && a[end - 2] as int == x {
                Self::count_x_segments(a, x, end - 1)
            } else {
                Self::count_x_segments(a, x, end - 1) + 1
            }
        } else {
            Self::count_x_segments(a, x, end - 1)
        }
    }

    pub open spec fn min_ops_for_value(a: Seq<i64>, x: int) -> nat {
        let segs = Self::count_x_segments(a, x, a.len() as int);
        if segs == 0 {
            (a.len() + 1) as nat
        } else {
            let left = if a[0] as int == x { 1int } else { 0int };
            let right = if a[a.len() - 1] as int == x { 1int } else { 0int };
            (segs as int + 1 - left - right) as nat
        }
    }

    pub open spec fn min_ops_upto(a: Seq<i64>, x_end: int) -> nat
        decreases x_end,
    {
        if x_end <= 0 {
            (a.len() + 1) as nat
        } else {
            let prev = Self::min_ops_upto(a, x_end - 1);
            let cur = Self::min_ops_for_value(a, x_end);
            if cur < prev { cur } else { prev }
        }
    }

    pub open spec fn min_operations(a: Seq<i64>) -> nat {
        Self::min_ops_upto(a, a.len() as int)
    }

    proof fn lemma_count_segments_step(a: Seq<i64>, x: int, end: int)
        requires
            0 <= end < a.len(),
        ensures
            Self::count_x_segments(a, x, end + 1)
                == Self::count_x_segments(a, x, end)
                    + if a[end] as int == x && (end == 0 || a[end - 1] as int != x) { 1nat } else { 0nat },
    {
        reveal_with_fuel(Solution::count_x_segments, 2);
    }

    proof fn lemma_count_segments_bounded(a: Seq<i64>, x: int, end: int)
        requires
            0 <= end <= a.len(),
        ensures
            Self::count_x_segments(a, x, end) <= end as nat,
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_segments_bounded(a, x, end - 1);
            Self::lemma_count_segments_step(a, x, end - 1);
        }
    }

    pub fn min_ops(a: Vec<i64>) -> (result: u64)
        requires
            1 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= a.len(),
        ensures
            result as int == Self::min_operations(a@),
    {
        let n = a.len();
        let ghost orig = a@;
        let mut segments: Vec<u64> = Vec::new();
        let mut init: usize = 0;

        while init <= n
            invariant
                n == a.len(),
                a@ == orig,
                n >= 1,
                n <= 200_000,
                0 <= init <= n + 1,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] orig[k] <= n,
                segments.len() == init,
                forall |v: int| 0 <= v < init ==> #[trigger] segments@[v] == 0,
            decreases n + 1 - init,
        {
            segments.push(0);
            init = init + 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                a@ == orig,
                n >= 1,
                n <= 200_000,
                0 <= i <= n,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] orig[k] <= n,
                segments.len() == n + 1,
                forall |v: int| 0 <= v <= n ==> #[trigger] segments@[v] as int == Self::count_x_segments(orig, v, i as int),
            decreases n - i,
        {
            if i == 0 || a[i] != a[i - 1] {
                let idx = a[i] as usize;
                let ghost prev_segments = segments@;
                proof {
                    assert(1 <= idx <= n);
                    Self::lemma_count_segments_bounded(orig, idx as int, i as int);
                    assert(prev_segments[idx as int] as nat <= i as nat);
                }
                let cur = segments[idx];
                segments.set(idx, segments[idx] + 1);
                proof {
                    assert forall |v: int| 0 <= v <= n implies #[trigger] segments@[v] as int == Self::count_x_segments(orig, v, i as int + 1) by {
                        Self::lemma_count_segments_step(orig, v, i as int);
                        if v == idx as int {
                            assert(prev_segments[v] == cur);
                            assert(segments@[v] == prev_segments[v] + 1);
                            assert(a[i as int] as int == v);
                            if i > 0 {
                                assert(a[i as int - 1] as int != v);
                            }
                        } else {
                            assert(segments@[v] == prev_segments[v]);
                            assert(a[i as int] as int != v);
                        }
                    };
                }
            } else {
                proof {
                    assert forall |v: int| 0 <= v <= n implies #[trigger] segments@[v] as int == Self::count_x_segments(orig, v, i as int + 1) by {
                        Self::lemma_count_segments_step(orig, v, i as int);
                        assert(segments@[v] as int == Self::count_x_segments(orig, v, i as int));
                        if a[i as int] as int == v {
                            assert(i > 0);
                            assert(a[i as int - 1] as int == v);
                        }
                    };
                }
            }
            i = i + 1;
        }

        let mut best: u64 = (n + 1) as u64;
        let mut x: usize = 1;
        while x <= n
            invariant
                n == a.len(),
                a@ == orig,
                n >= 1,
                n <= 200_000,
                1 <= x <= n + 1,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] orig[k] <= n,
                segments.len() == n + 1,
                forall |v: int| 0 <= v <= n ==> #[trigger] segments@[v] as int == Self::count_x_segments(orig, v, n as int),
                best as int == Self::min_ops_upto(orig, x as int - 1),
                best as nat <= (n + 1) as nat,
            decreases n + 1 - x,
        {
            let ghost prev_best = best;
            if segments[x] > 0 {
                proof {
                    Self::lemma_count_segments_bounded(orig, x as int, n as int);
                    assert(segments@[x as int] as nat <= n as nat);
                    assert(segments@[x as int] < 18446744073709551615u64);
                }
                let mut ops = segments[x] + 1;
                if a[0] == x as i64 {
                    assert(ops > 0);
                    ops = ops - 1;
                }
                if a[n - 1] == x as i64 {
                    assert(ops > 0);
                    ops = ops - 1;
                }
                if ops < best {
                    best = ops;
                }
                proof {
                    let prev = Self::min_ops_upto(orig, x as int - 1);
                    let cur = Self::min_ops_for_value(orig, x as int);
                    assert(prev_best as int == prev);
                    assert(segments@[x as int] as int == Self::count_x_segments(orig, x as int, n as int));
                    assert(Self::count_x_segments(orig, x as int, n as int) > 0);
                    assert(cur
                        == ({
                            let segs = Self::count_x_segments(orig, x as int, n as int);
                            let left = if orig[0] as int == x as int { 1int } else { 0int };
                            let right = if orig[n as int - 1] as int == x as int { 1int } else { 0int };
                            (segs as int + 1 - left - right) as nat
                        }));
                    assert(ops as int == cur as int);
                    assert(best as int == if cur < prev { cur } else { prev });
                }
            } else {
                proof {
                    let prev = Self::min_ops_upto(orig, x as int - 1);
                    let cur = Self::min_ops_for_value(orig, x as int);
                    assert(prev_best as int == prev);
                    assert(Self::count_x_segments(orig, x as int, n as int) == 0);
                    assert(cur == (n + 1) as nat);
                    assert(prev <= (n + 1) as nat);
                    assert(best == prev_best);
                    assert(best as int == if cur < prev { cur } else { prev });
                }
            }
            x = x + 1;
        }

        proof {
            assert(best as int == Self::min_ops_upto(orig, n as int));
        }
        best
    }
}

}
