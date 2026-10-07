use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn delta_step(base: i64, other: i64) -> int {
        if other < base {
            -1
        } else if other > base {
            1
        } else {
            0
        }
    }

    pub open spec fn shift_delta(a: Seq<i64>, l: int, r: int) -> int
        recommends
            0 <= l <= r < a.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::shift_delta(a, l, r - 1) + Self::delta_step(a[l], a[r])
        }
    }

    proof fn lemma_shift_delta_step(a: Seq<i64>, l: int, r: int)
        requires
            0 <= l < r < a.len(),
        ensures
            Self::shift_delta(a, l, r) == Self::shift_delta(a, l, r - 1) + Self::delta_step(a[l], a[r]),
    {
    }

    pub fn best_shift(a: Vec<i64>) -> (result: (usize, usize))
        requires
            1 <= a.len() <= 2000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 2000,
        ensures
            0 <= result.0 <= result.1 < a.len(),
            forall|l: int, r: int| 0 <= l <= r < a.len() ==> Self::shift_delta(a@, result.0 as int, result.1 as int) <= #[trigger] Self::shift_delta(a@, l, r),
    {
        let n = a.len();
        let ghost orig = a@;
        let mut best_l: usize = 0;
        let mut best_r: usize = 0;
        let mut best_delta: i64 = 0;
        let mut l: usize = 0;
        while l < n
            invariant
                n == a.len(),
                orig == a@,
                1 <= n <= 2000,
                0 <= l <= n,
                0 <= best_l <= best_r < n,
                best_delta as int == Self::shift_delta(orig, best_l as int, best_r as int),
                best_delta as int <= 0,
                forall|i: int| 0 <= i < n ==> 1 <= #[trigger] orig[i] <= 2000,
                forall|ll: int, rr: int| 0 <= ll < l && ll <= rr < n ==> Self::shift_delta(orig, best_l as int, best_r as int) <= #[trigger] Self::shift_delta(orig, ll, rr),
            decreases n - l,
        {
            let mut cur_delta: i64 = 0;
            let mut r: usize = l + 1;
            while r < n
                invariant
                    n == a.len(),
                    orig == a@,
                    1 <= n <= 2000,
                    0 <= l < n,
                    l + 1 <= r <= n,
                    0 <= best_l <= best_r < n,
                    best_delta as int == Self::shift_delta(orig, best_l as int, best_r as int),
                    best_delta as int <= 0,
                    cur_delta as int == if r == l + 1 { 0 } else { Self::shift_delta(orig, l as int, r as int - 1) },
                    -((r as int) - (l as int) - 1) <= cur_delta as int <= ((r as int) - (l as int) - 1),
                    forall|i: int| 0 <= i < n ==> 1 <= #[trigger] orig[i] <= 2000,
                    forall|ll: int, rr: int| 0 <= ll < l && ll <= rr < n ==> Self::shift_delta(orig, best_l as int, best_r as int) <= #[trigger] Self::shift_delta(orig, ll, rr),
                    forall|rr: int| l as int <= rr < r as int ==> Self::shift_delta(orig, best_l as int, best_r as int) <= #[trigger] Self::shift_delta(orig, l as int, rr),
                decreases n - r,
            {
                let old_cur_delta = cur_delta;
                if a[r] < a[l] {
                    cur_delta = cur_delta - 1;
                } else if a[r] > a[l] {
                    cur_delta = cur_delta + 1;
                }
                proof {
                    assert(-((r as int) - (l as int)) <= cur_delta as int <= ((r as int) - (l as int)));
                    if r > l + 1 {
                        Self::lemma_shift_delta_step(orig, l as int, r as int);
                        assert(old_cur_delta as int == Self::shift_delta(orig, l as int, r as int - 1));
                    } else {
                        assert(r == l + 1);
                        assert(old_cur_delta == 0);
                    }
                    assert(cur_delta as int == old_cur_delta as int + Self::delta_step(orig[l as int], orig[r as int]));
                    assert(cur_delta as int == Self::shift_delta(orig, l as int, r as int));
                }
                if cur_delta < best_delta {
                    best_delta = cur_delta;
                    best_l = l;
                    best_r = r;
                }
                proof {
                    assert(best_delta as int <= 0);
                    assert(best_delta as int == Self::shift_delta(orig, best_l as int, best_r as int));
                    assert forall|rr: int| l as int <= rr <= r as int implies Self::shift_delta(orig, best_l as int, best_r as int) <= #[trigger] Self::shift_delta(orig, l as int, rr) by {
                        if rr < r as int {
                        } else {
                            assert(cur_delta as int == Self::shift_delta(orig, l as int, rr));
                        }
                    }
                }
                r = r + 1;
            }
            l = l + 1;
        }
        (best_l, best_r)
    }
}

}
