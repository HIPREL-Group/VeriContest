use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

pub open spec fn sum_dist(x1: int, x2: int, x3: int, m: int) -> int {
    abs_diff(x1, m) + abs_diff(x2, m) + abs_diff(x3, m)
}

pub open spec fn min3(a: int, b: int, c: int) -> int {
    if a <= b && a <= c {
        a
    } else if b <= a && b <= c {
        b
    } else {
        c
    }
}

pub open spec fn max3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c {
        a
    } else if b >= a && b >= c {
        b
    } else {
        c
    }
}

proof fn lemma_abs_diff_nonneg(a: int, b: int)
    ensures abs_diff(a, b) >= 0,
{
    if a >= b {
        assert(abs_diff(a, b) == a - b);
    } else {
        assert(abs_diff(a, b) == b - a);
    }
}

proof fn lemma_abs_triangle_line(a: int, b: int, m: int)
    ensures abs_diff(a, m) + abs_diff(b, m) >= abs_diff(a, b),
{
    if a >= b {
        assert(abs_diff(a, b) == a - b);
        if m >= a {
            assert(abs_diff(a, m) == m - a);
            assert(abs_diff(b, m) == m - b);
            assert(abs_diff(a, m) + abs_diff(b, m) == 2 * m - a - b);
            assert(2 * m - a - b >= a - b);
        } else if m <= b {
            assert(abs_diff(a, m) == a - m);
            assert(abs_diff(b, m) == b - m);
            assert(abs_diff(a, m) + abs_diff(b, m) == a + b - 2 * m);
            assert(a + b - 2 * m >= a - b);
        } else {
            assert(b < m && m < a);
            assert(abs_diff(a, m) == a - m);
            assert(abs_diff(b, m) == m - b);
            assert(abs_diff(a, m) + abs_diff(b, m) == a - b);
        }
    } else {
        assert(b > a);
        assert(abs_diff(a, b) == b - a);
        if m >= b {
            assert(abs_diff(a, m) == m - a);
            assert(abs_diff(b, m) == m - b);
            assert(abs_diff(a, m) + abs_diff(b, m) == 2 * m - a - b);
            assert(2 * m - a - b >= b - a);
        } else if m <= a {
            assert(abs_diff(a, m) == a - m);
            assert(abs_diff(b, m) == b - m);
            assert(abs_diff(a, m) + abs_diff(b, m) == a + b - 2 * m);
            assert(a + b - 2 * m >= b - a);
        } else {
            assert(a < m && m < b);
            assert(abs_diff(a, m) == m - a);
            assert(abs_diff(b, m) == b - m);
            assert(abs_diff(a, m) + abs_diff(b, m) == b - a);
        }
    }
}

proof fn lemma_sum_dist_perm6(
    x1: int,
    x2: int,
    x3: int,
    mn: int,
    med: int,
    mx: int,
    m: int,
)
    requires
        mn < med,
        med < mx,
        x1 != x2,
        x1 != x3,
        x2 != x3,
        (x1 == mn && x2 == med && x3 == mx) || (x1 == mn && x2 == mx && x3 == med)
            || (x1 == med && x2 == mn && x3 == mx) || (x1 == med && x2 == mx && x3 == mn)
            || (x1 == mx && x2 == mn && x3 == med) || (x1 == mx && x2 == med && x3 == mn),
    ensures
        sum_dist(x1, x2, x3, m) == abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m),
{
    if x1 == mn && x2 == med && x3 == mx {
        assert(sum_dist(x1, x2, x3, m) == abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m));
    } else if x1 == mn && x2 == mx && x3 == med {
        assert(sum_dist(x1, x2, x3, m) == abs_diff(mn, m) + abs_diff(mx, m) + abs_diff(med, m));
        assert(abs_diff(mn, m) + abs_diff(mx, m) + abs_diff(med, m) == abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m));
    } else if x1 == med && x2 == mn && x3 == mx {
        assert(sum_dist(x1, x2, x3, m) == abs_diff(med, m) + abs_diff(mn, m) + abs_diff(mx, m));
        assert(abs_diff(med, m) + abs_diff(mn, m) + abs_diff(mx, m) == abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m));
    } else if x1 == med && x2 == mx && x3 == mn {
        assert(sum_dist(x1, x2, x3, m) == abs_diff(med, m) + abs_diff(mx, m) + abs_diff(mn, m));
        assert(abs_diff(med, m) + abs_diff(mx, m) + abs_diff(mn, m) == abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m));
    } else if x1 == mx && x2 == mn && x3 == med {
        assert(sum_dist(x1, x2, x3, m) == abs_diff(mx, m) + abs_diff(mn, m) + abs_diff(med, m));
        assert(abs_diff(mx, m) + abs_diff(mn, m) + abs_diff(med, m) == abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m));
    } else {
        assert(x1 == mx && x2 == med && x3 == mn);
        assert(sum_dist(x1, x2, x3, m) == abs_diff(mx, m) + abs_diff(med, m) + abs_diff(mn, m));
        assert(abs_diff(mx, m) + abs_diff(med, m) + abs_diff(mn, m) == abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m));
    }
}

proof fn lemma_sum_dist_ge_spread(
    x1: int,
    x2: int,
    x3: int,
    mn: int,
    med: int,
    mx: int,
    m: int,
)
    requires
        mn < med,
        med < mx,
        x1 != x2,
        x1 != x3,
        x2 != x3,
        (x1 == mn && x2 == med && x3 == mx) || (x1 == mn && x2 == mx && x3 == med)
            || (x1 == med && x2 == mn && x3 == mx) || (x1 == med && x2 == mx && x3 == mn)
            || (x1 == mx && x2 == mn && x3 == med) || (x1 == mx && x2 == med && x3 == mn),
    ensures
        sum_dist(x1, x2, x3, m) >= mx - mn,
{
    lemma_sum_dist_perm6(x1, x2, x3, mn, med, mx, m);
    lemma_abs_diff_nonneg(med, m);
    assert(abs_diff(med, m) >= 0);
    assert(sum_dist(x1, x2, x3, m) == abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m));
    assert(abs_diff(mn, m) + abs_diff(med, m) + abs_diff(mx, m) >= abs_diff(mn, m) + abs_diff(mx, m));
    lemma_abs_triangle_line(mn, mx, m);
    assert(abs_diff(mn, m) + abs_diff(mx, m) >= abs_diff(mn, mx));
    assert(abs_diff(mn, mx) == mx - mn);
}

proof fn lemma_sum_at_median(x1: int, x2: int, x3: int, mn: int, med: int, mx: int)
    requires
        mn < med,
        med < mx,
        x1 != x2,
        x1 != x3,
        x2 != x3,
        (x1 == mn && x2 == med && x3 == mx) || (x1 == mn && x2 == mx && x3 == med)
            || (x1 == med && x2 == mn && x3 == mx) || (x1 == med && x2 == mx && x3 == mn)
            || (x1 == mx && x2 == mn && x3 == med) || (x1 == mx && x2 == med && x3 == mn),
    ensures
        sum_dist(x1, x2, x3, med) == mx - mn,
{
    lemma_sum_dist_perm6(x1, x2, x3, mn, med, mx, med);
    assert(abs_diff(mn, med) == med - mn);
    assert(abs_diff(med, med) == 0);
    assert(abs_diff(mx, med) == mx - med);
    assert(abs_diff(mn, med) + abs_diff(med, med) + abs_diff(mx, med) == (med - mn) + (mx - med));
    assert((med - mn) + (mx - med) == mx - mn);
    assert(sum_dist(x1, x2, x3, med) == mx - mn);
}

proof fn lemma_mn_equals_min3(x1: int, x2: int, x3: int, mn: int)
    requires
        mn <= x1,
        mn <= x2,
        mn <= x3,
        x1 == mn || x2 == mn || x3 == mn,
    ensures
        mn == min3(x1, x2, x3),
{
    if x1 <= x2 && x1 <= x3 {
        assert(x1 == mn);
        assert(min3(x1, x2, x3) == x1);
    } else if x2 <= x1 && x2 <= x3 {
        assert(x2 == mn);
        assert(min3(x1, x2, x3) == x2);
    } else {
        assert(x3 == mn);
        assert(min3(x1, x2, x3) == x3);
    }
}

proof fn lemma_mx_equals_max3(x1: int, x2: int, x3: int, mx: int)
    requires
        mx >= x1,
        mx >= x2,
        mx >= x3,
        x1 == mx || x2 == mx || x3 == mx,
    ensures
        mx == max3(x1, x2, x3),
{
    if x1 >= x2 && x1 >= x3 {
        assert(x1 == mx);
        assert(max3(x1, x2, x3) == x1);
    } else if x2 >= x1 && x2 >= x3 {
        assert(x2 == mx);
        assert(max3(x1, x2, x3) == x2);
    } else {
        assert(x3 == mx);
        assert(max3(x1, x2, x3) == x3);
    }
}

proof fn lemma_distinct_triple_perm(x1: int, x2: int, x3: int, mn: int, med: int, mx: int)
    requires
        mn < med,
        med < mx,
        x1 != x2,
        x1 != x3,
        x2 != x3,
        (x1 == mn || x1 == med || x1 == mx),
        (x2 == mn || x2 == med || x2 == mx),
        (x3 == mn || x3 == med || x3 == mx),
    ensures
        (x1 == mn && x2 == med && x3 == mx) || (x1 == mn && x2 == mx && x3 == med)
            || (x1 == med && x2 == mn && x3 == mx) || (x1 == med && x2 == mx && x3 == mn)
            || (x1 == mx && x2 == mn && x3 == med) || (x1 == mx && x2 == med && x3 == mn),
{
    if x1 == mn {
        if x2 == med {
            assert(x3 == mx);
        } else {
            assert(x2 == mx);
            assert(x3 == med);
        }
    } else if x1 == med {
        if x2 == mn {
            assert(x3 == mx);
        } else {
            assert(x2 == mx);
            assert(x3 == mn);
        }
    } else {
        assert(x1 == mx);
        if x2 == mn {
            assert(x3 == med);
        } else {
            assert(x2 == med);
            assert(x3 == mn);
        }
    }
}

proof fn lemma_middle_value(x1: int, x2: int, x3: int, mn: int, mx: int) -> (med: int)
    requires
        1 <= x1 <= 100,
        1 <= x2 <= 100,
        1 <= x3 <= 100,
        x1 != x2,
        x1 != x3,
        x2 != x3,
        mn == min3(x1, x2, x3),
        mx == max3(x1, x2, x3),
    ensures
        mn < med,
        med < mx,
        (x1 == mn && x2 == med && x3 == mx) || (x1 == mn && x2 == mx && x3 == med)
            || (x1 == med && x2 == mn && x3 == mx) || (x1 == med && x2 == mx && x3 == mn)
            || (x1 == mx && x2 == mn && x3 == med) || (x1 == mx && x2 == med && x3 == mn),
{
    assert(mn < mx);
    let r = if (x1 != mn && x1 != mx) {
        x1
    } else if (x2 != mn && x2 != mx) {
        x2
    } else {
        assert(x3 != mn && x3 != mx);
        x3
    };
    assert(mn < r && r < mx);
    assert(x1 == mn || x1 == r || x1 == mx);
    assert(x2 == mn || x2 == r || x2 == mx);
    assert(x3 == mn || x3 == r || x3 == mx);
    lemma_distinct_triple_perm(x1, x2, x3, mn, r, mx);
    r
}

impl Solution {
    pub fn min_total_meeting_distance(x1: i32, x2: i32, x3: i32) -> (res: i32)
        requires
            1 <= x1 as int <= 100,
            1 <= x2 as int <= 100,
            1 <= x3 as int <= 100,
            x1 as int != x2 as int,
            x1 as int != x3 as int,
            x2 as int != x3 as int,
        ensures
            2 <= res as int <= 99,
            forall |m: int| #[trigger] sum_dist(x1 as int, x2 as int, x3 as int, m) >= res as int,
            exists |m: int| #[trigger] sum_dist(x1 as int, x2 as int, x3 as int, m) == res as int,
    {
        let mut coords: Vec<i32> = Vec::new();
        coords.push(x1);
        coords.push(x2);
        coords.push(x3);
        let mut mn = coords[0];
        let mut mx = coords[0];
        let mut i = 1usize;
        proof {
            assert(mn == coords@[0] && mx == coords@[0]);
            assert(exists |ka: int| 0 <= ka < 1 && coords@[ka] as int == mn as int);
            assert(exists |kb: int| 0 <= kb < 1 && coords@[kb] as int == mx as int);
        }
        while i < 3
            invariant
                coords.len() == 3,
                coords@[0] == x1,
                coords@[1] == x2,
                coords@[2] == x3,
                1 <= i <= 3,
                forall |k: int|
                    0 <= k < i as int ==> mn as int <= coords@[k] as int && coords@[k] as int <= mx as int,
                exists |ka: int|
                    0 <= ka < i as int && coords@[ka] as int == mn as int,
                exists |kb: int|
                    0 <= kb < i as int && coords@[kb] as int == mx as int,
            decreases 3 - i,
        {
            let ghost old_mn = mn;
            let ghost old_mx = mx;
            proof {
                assert(i == 1 || i == 2);
            }
            if coords[i] < mn {
                mn = coords[i];
            }
            if coords[i] > mx {
                mx = coords[i];
            }
            proof {
                assert(exists |ka: int| 0 <= ka < i as int + 1 && coords@[ka] as int == mn as int) by {
                    if mn == old_mn {
                        assert(exists |ka: int| 0 <= ka < i as int && coords@[ka] as int == old_mn as int);
                    } else {
                        assert(mn == coords@[i as int]);
                        assert(coords@[i as int] as int == mn as int);
                        let ii = i as int;
                        assert(0 <= ii && ii < ii + 1);
                    }
                };
                assert(exists |kb: int| 0 <= kb < i as int + 1 && coords@[kb] as int == mx as int) by {
                    if mx == old_mx {
                        assert(exists |kb: int| 0 <= kb < i as int && coords@[kb] as int == old_mx as int);
                    } else {
                        assert(mx == coords@[i as int]);
                        assert(coords@[i as int] as int == mx as int);
                        let ii = i as int;
                        assert(0 <= ii && ii < ii + 1);
                    }
                };
            }
            i = i + 1;
        }
        proof {
            assert(i == 3);
            assert(forall |k: int|
                0 <= k < 3 ==> mn as int <= coords@[k] as int && coords@[k] as int <= mx as int);
            assert(exists |ka: int| 0 <= ka < 3 && coords@[ka] as int == mn as int);
            assert(exists |kb: int| 0 <= kb < 3 && coords@[kb] as int == mx as int);
            lemma_mn_equals_min3(x1 as int, x2 as int, x3 as int, mn as int);
            lemma_mx_equals_max3(x1 as int, x2 as int, x3 as int, mx as int);
            let med = lemma_middle_value(x1 as int, x2 as int, x3 as int, mn as int, mx as int);
            assert(2 <= (mx as int - mn as int) <= 99);
            assert forall|m: int|
                sum_dist(x1 as int, x2 as int, x3 as int, m) >= (mx as int - mn as int) by {
                lemma_sum_dist_ge_spread(
                    x1 as int,
                    x2 as int,
                    x3 as int,
                    mn as int,
                    med,
                    mx as int,
                    m,
                );
            };
            lemma_sum_at_median(x1 as int, x2 as int, x3 as int, mn as int, med, mx as int);
            assert(exists |m: int|
                sum_dist(x1 as int, x2 as int, x3 as int, m) == (mx as int - mn as int)) by {
                assert(sum_dist(x1 as int, x2 as int, x3 as int, med) == (mx as int - mn as int));
            };
            assert(forall |m: int|
                sum_dist(x1 as int, x2 as int, x3 as int, m) >= (mx as int - mn as int));
            assert(exists |m: int|
                sum_dist(x1 as int, x2 as int, x3 as int, m) == (mx as int - mn as int));
        }
        mx - mn
    }
}

}

