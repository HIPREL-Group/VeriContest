use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_int(v: int) -> int {
        if v >= 0 { v } else { -v }
    }

    pub open spec fn valid_x(a: Seq<i32>, x: int) -> bool {
        forall|i: int| 0 <= i && i + 1 < a.len() ==> #[trigger] Self::abs_int(a[i] as int - x) <= Self::abs_int(a[i + 1] as int - x)
    }

    pub open spec fn inc_pair(a: Seq<i32>, k: int) -> bool
        recommends
            0 <= k + 1 < a.len(),
    {
        (a[k] as int) < (a[k + 1] as int)
    }

    pub open spec fn dec_pair(a: Seq<i32>, k: int) -> bool
        recommends
            0 <= k + 1 < a.len(),
    {
        (a[k] as int) > (a[k + 1] as int)
    }

    pub open spec fn ub_pair(a: Seq<i32>, k: int) -> int
        recommends
            0 <= k + 1 < a.len(),
    {
        (a[k] as int + a[k + 1] as int) / 2
    }

    pub open spec fn lb_pair(a: Seq<i32>, k: int) -> int
        recommends
            0 <= k + 1 < a.len(),
    {
        (a[k] as int + a[k + 1] as int + 1) / 2
    }

    pub proof fn lemma_inc(a: int, b: int, x: int)
        requires
            0 <= a < b,
            0 <= x,
            x <= (a + b) / 2,
        ensures
            Self::abs_int(a - x) <= Self::abs_int(b - x),
    {
        assert(2 * x <= a + b);
        if x <= a {
            assert(Self::abs_int(a - x) == a - x);
            assert(Self::abs_int(b - x) == b - x);
            assert(a - x <= b - x);
        } else {
            assert(a < x);
            assert(2 * b > a + b);
            assert(2 * x <= a + b);
            assert(x <= b);
            assert(Self::abs_int(a - x) == x - a);
            assert(Self::abs_int(b - x) == b - x);
            assert(x - a <= b - x);
        }
    }

    pub proof fn lemma_dec(a: int, b: int, x: int)
        requires
            0 <= b < a,
            0 <= x,
            (a + b + 1) / 2 <= x,
        ensures
            Self::abs_int(a - x) <= Self::abs_int(b - x),
    {
        assert(a + b <= 2 * x);
        if x >= a {
            assert(Self::abs_int(a - x) == x - a);
            assert(Self::abs_int(b - x) == x - b);
            assert(x - a <= x - b);
        } else {
            assert(x < a);
            assert(2 * b < a + b + 1);
            assert(a + b + 1 <= 2 * x + 1);
            assert(b <= x);
            assert(Self::abs_int(a - x) == a - x);
            assert(Self::abs_int(b - x) == x - b);
            assert(a - x <= x - b);
        }
    }

    pub fn absolute_sorting(a: Vec<i32>) -> (res: i32)
        requires
            2 <= a.len() <= 200000,
            forall|i: int| 0 <= i < a.len() as int ==> 0 <= #[trigger] a[i] <= 1000000000,
        ensures
            (res == -1) || (0 <= res <= 1000000000 && Self::valid_x(a@, res as int)),
    {
        let n = a.len();
        let mut low: i64 = 0;
        let mut high: i64 = 1000000000;
        let mut i: usize = 0;
        while i + 1 < n
            invariant
                2 <= n <= 200000,
                a.len() == n,
                0 <= i < n,
                0 <= low <= 1000000000,
                0 <= high <= 1000000000,
                forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] a[k] <= 1000000000,
                forall|k: int| 0 <= k && k < i as int && #[trigger] Self::inc_pair(a@, k) ==> high as int <= Self::ub_pair(a@, k),
                forall|k: int| 0 <= k && k < i as int && #[trigger] Self::dec_pair(a@, k) ==> Self::lb_pair(a@, k) <= low as int,
            decreases n - i,
        {
            let x = a[i] as i64;
            let y = a[i + 1] as i64;
            if x < y {
                let ub = (x + y) / 2;
                if ub < high {
                    high = ub;
                }
            } else if x > y {
                let lb = (x + y + 1) / 2;
                if lb > low {
                    low = lb;
                }
            }
            proof {
                assert(0 <= x <= 1000000000);
                assert(0 <= y <= 1000000000);
                assert(0 <= (x + y) / 2 <= 1000000000);
                assert(0 <= (x + y + 1) / 2 <= 1000000000);
            }
            i += 1;
        }
        if low <= high {
            proof {
                assert(0 <= low as int <= 1000000000);
                assert forall|k: int| 0 <= k && k + 1 < a.len() implies #[trigger] Self::abs_int(a[k] as int - low as int) <= Self::abs_int(a[k + 1] as int - low as int) by {
                    if Self::inc_pair(a@, k) {
                        assert(high as int <= Self::ub_pair(a@, k));
                        assert(low as int <= high as int);
                        assert(low as int <= Self::ub_pair(a@, k));
                        Self::lemma_inc(a[k] as int, a[k + 1] as int, low as int);
                    } else if Self::dec_pair(a@, k) {
                        assert(Self::lb_pair(a@, k) <= low as int);
                        Self::lemma_dec(a[k] as int, a[k + 1] as int, low as int);
                    } else {
                        assert(Self::abs_int(a[k] as int - low as int) == Self::abs_int(a[k + 1] as int - low as int));
                    }
                };
            }
            low as i32
        } else {
            -1
        }
    }
}

}
