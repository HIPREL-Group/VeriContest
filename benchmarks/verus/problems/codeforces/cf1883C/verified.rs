use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn has_even_upto(s: Seq<i32>, i: int) -> bool
    decreases i
{
    if i <= 0 {
        false
    } else {
        (s[i - 1] as int) % 2 == 0 || has_even_upto(s, i - 1)
    }
}

pub open spec fn min_ops_k2(s: Seq<i32>, n: int) -> int {
    if has_even_upto(s, n) {
        0
    } else {
        1
    }
}

pub open spec fn dist_mod3(x: int) -> int {
    let r = x % 3;
    if r == 0 {
        0
    } else {
        3 - r
    }
}

pub open spec fn min_dist_mod3_upto(s: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        3
    } else {
        let prev = min_dist_mod3_upto(s, i - 1);
        let x = s[i - 1] as int;
        let d = dist_mod3(x);
        if d < prev {
            d
        } else {
            prev
        }
    }
}

pub open spec fn dist_mod5(x: int) -> int {
    let r = x % 5;
    if r == 0 {
        0
    } else {
        5 - r
    }
}

pub open spec fn min_dist_mod5_upto(s: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        5
    } else {
        let prev = min_dist_mod5_upto(s, i - 1);
        let x = s[i - 1] as int;
        let d = dist_mod5(x);
        if d < prev {
            d
        } else {
            prev
        }
    }
}

pub open spec fn count_even_upto(s: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else {
        let add = if (s[i - 1] as int) % 2 == 0 {
            1int
        } else {
            0int
        };
        count_even_upto(s, i - 1) + add
    }
}

pub open spec fn has_div4_upto(s: Seq<i32>, i: int) -> bool
    decreases i
{
    if i <= 0 {
        false
    } else {
        (s[i - 1] as int) % 4 == 0 || has_div4_upto(s, i - 1)
    }
}

pub open spec fn has_three_mod4_upto(s: Seq<i32>, i: int) -> bool
    decreases i
{
    if i <= 0 {
        false
    } else {
        (s[i - 1] as int) % 4 == 3 || has_three_mod4_upto(s, i - 1)
    }
}

pub open spec fn min_ops_k4(s: Seq<i32>, n: int) -> int {
    if has_div4_upto(s, n) {
        0
    } else if count_even_upto(s, n) >= 2 {
        0
    } else if count_even_upto(s, n) == 1 {
        1
    } else if has_three_mod4_upto(s, n) {
        1
    } else {
        2
    }
}

pub open spec fn expected_min_ops(k: int, s: Seq<i32>, n: int) -> int {
    if k == 2 {
        min_ops_k2(s, n)
    } else if k == 3 {
        min_dist_mod3_upto(s, n)
    } else if k == 4 {
        min_ops_k4(s, n)
    } else if k == 5 {
        min_dist_mod5_upto(s, n)
    } else {
        0
    }
}

proof fn lemma_count_even_bounded(s: Seq<i32>, i: int)
    requires
        i >= 0,
    ensures
        count_even_upto(s, i) <= i,
    decreases i
{
    if i > 0 {
        lemma_count_even_bounded(s, i - 1);
    }
}

proof fn lemma_count_even_nonneg(s: Seq<i32>, i: int)
    requires
        i >= 0,
    ensures
        count_even_upto(s, i) >= 0,
    decreases i
{
    if i > 0 {
        lemma_count_even_nonneg(s, i - 1);
    }
}

proof fn lemma_has_even_unfold(s: Seq<i32>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        has_even_upto(s, i + 1) == (has_even_upto(s, i) || (s[i] as int) % 2 == 0)
{
}

proof fn lemma_min_dist3_unfold(s: Seq<i32>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        min_dist_mod3_upto(s, i + 1) == ({
            let prev = min_dist_mod3_upto(s, i);
            let x = s[i] as int;
            let d = dist_mod3(x);
            if d < prev {
                d
            } else {
                prev
            }
        })
{
}

proof fn lemma_min_dist5_unfold(s: Seq<i32>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        min_dist_mod5_upto(s, i + 1) == ({
            let prev = min_dist_mod5_upto(s, i);
            let x = s[i] as int;
            let d = dist_mod5(x);
            if d < prev {
                d
            } else {
                prev
            }
        })
{
}

proof fn lemma_count_even_unfold(s: Seq<i32>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        count_even_upto(s, i + 1) == count_even_upto(s, i) + (if (s[i] as int) % 2 == 0 {
            1int
        } else {
            0int
        })
{
}

proof fn lemma_has_div4_unfold(s: Seq<i32>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        has_div4_upto(s, i + 1) == (has_div4_upto(s, i) || (s[i] as int) % 4 == 0)
{
}

proof fn lemma_has_three_mod4_unfold(s: Seq<i32>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        has_three_mod4_upto(s, i + 1) == (has_three_mod4_upto(s, i) || (s[i] as int) % 4 == 3)
{
}

pub struct Solution;

impl Solution {
    pub fn min_ops(n: usize, k: i32, a: Vec<i32>) -> (res: i32)
        requires
            2 <= n && n <= 100000,
            2 <= k && k <= 5,
            a.len() == n,
            forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 10,
        ensures
            res == expected_min_ops(k as int, a@, n as int)
    {
        if k == 2 {
            let mut any_even = false;
            let mut i: usize = 0;
            while i < n
                invariant
                    0 <= i && i <= n,
                    a.len() == n,
                    forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 10,
                    any_even == has_even_upto(a@, i as int),
                decreases n - i
            {
                proof {
                    lemma_has_even_unfold(a@, i as int);
                }
                if a[i] % 2 == 0 {
                    any_even = true;
                }
                proof {
                    assert(any_even == has_even_upto(a@, (i + 1) as int));
                }
                i += 1;
            }
            if any_even {
                proof {
                    assert(has_even_upto(a@, n as int));
                    assert(min_ops_k2(a@, n as int) == 0);
                    assert(expected_min_ops(2, a@, n as int) == 0);
                }
                0
            } else {
                proof {
                    assert(!has_even_upto(a@, n as int));
                    assert(min_ops_k2(a@, n as int) == 1);
                    assert(expected_min_ops(2, a@, n as int) == 1);
                }
                1
            }
        } else if k == 3 {
            let mut best: i32 = 3;
            let mut i: usize = 0;
            while i < n
                invariant
                    0 <= i && i <= n,
                    a.len() == n,
                    forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 10,
                    best == min_dist_mod3_upto(a@, i as int),
                decreases n - i
            {
                proof {
                    lemma_min_dist3_unfold(a@, i as int);
                }
                let x = a[i];
                let r = x % 3;
                let cost = if r == 0 { 0 } else { 3 - r };
                if cost < best {
                    best = cost;
                }
                proof {
                    assert(best == min_dist_mod3_upto(a@, (i + 1) as int));
                }
                i += 1;
            }
            proof {
                assert(best == min_dist_mod3_upto(a@, n as int));
                assert(expected_min_ops(3, a@, n as int) == min_dist_mod3_upto(a@, n as int));
            }
            best
        } else if k == 5 {
            let mut best: i32 = 5;
            let mut i: usize = 0;
            while i < n
                invariant
                    0 <= i && i <= n,
                    a.len() == n,
                    forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 10,
                    best == min_dist_mod5_upto(a@, i as int),
                decreases n - i
            {
                proof {
                    lemma_min_dist5_unfold(a@, i as int);
                }
                let x = a[i];
                let r = x % 5;
                let cost = if r == 0 { 0 } else { 5 - r };
                if cost < best {
                    best = cost;
                }
                proof {
                    assert(best == min_dist_mod5_upto(a@, (i + 1) as int));
                }
                i += 1;
            }
            proof {
                assert(best == min_dist_mod5_upto(a@, n as int));
                assert(expected_min_ops(5, a@, n as int) == min_dist_mod5_upto(a@, n as int));
            }
            best
        } else {
            proof {
                assert(k == 4);
            }
            let mut cnt_even: i32 = 0;
            let mut has4 = false;
            let mut has3mod4 = false;
            let mut i: usize = 0;
            while i < n
                invariant
                    0 <= i && i <= n,
                    2 <= n && n <= 100000,
                    a.len() == n,
                    forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 10,
                    cnt_even as int == count_even_upto(a@, i as int),
                    (cnt_even as int) <= i as int,
                    cnt_even >= 0,
                    has4 == has_div4_upto(a@, i as int),
                    has3mod4 == has_three_mod4_upto(a@, i as int),
                decreases n - i
            {
                let old_c = cnt_even;
                proof {
                    lemma_count_even_unfold(a@, i as int);
                    lemma_has_div4_unfold(a@, i as int);
                    lemma_has_three_mod4_unfold(a@, i as int);
                    lemma_count_even_bounded(a@, i as int);
                }
                let x = a[i];
                if x % 4 == 0 {
                    has4 = true;
                }
                if x % 4 == 3 {
                    has3mod4 = true;
                }
                if x % 2 == 0 {
                    proof {
                        assert((old_c as int) == count_even_upto(a@, i as int));
                        assert((old_c as int) <= (i as int));
                        assert((i as int) < (n as int));
                        assert((old_c as int) + 1 <= (n as int));
                        assert((n as int) <= 100000);
                        assert((old_c as int) + 1 <= 100000);
                        assert(old_c < 2147483647);
                    }
                    cnt_even = old_c + 1;
                    proof {
                        assert((cnt_even as int) == count_even_upto(a@, (i + 1) as int));
                    }
                } else {
                    proof {
                        assert((cnt_even as int) == count_even_upto(a@, (i + 1) as int));
                    }
                }
                proof {
                    lemma_count_even_nonneg(a@, (i + 1) as int);
                    assert(has4 == has_div4_upto(a@, (i + 1) as int));
                    assert(has3mod4 == has_three_mod4_upto(a@, (i + 1) as int));
                    assert((cnt_even as int) <= (i + 1) as int);
                    assert(cnt_even >= 0);
                }
                i += 1;
            }
            if has4 {
                proof {
                    assert(has_div4_upto(a@, n as int));
                    assert(min_ops_k4(a@, n as int) == 0);
                    assert(expected_min_ops(4, a@, n as int) == 0);
                }
                0
            } else if cnt_even >= 2 {
                proof {
                    assert(!has_div4_upto(a@, n as int));
                    assert((cnt_even as int) >= 2);
                    assert(count_even_upto(a@, n as int) >= 2);
                    assert(min_ops_k4(a@, n as int) == 0);
                    assert(expected_min_ops(4, a@, n as int) == 0);
                }
                0
            } else if cnt_even == 1 {
                proof {
                    assert(!has_div4_upto(a@, n as int));
                    assert((cnt_even as int) == 1);
                    assert(count_even_upto(a@, n as int) == 1);
                    assert(min_ops_k4(a@, n as int) == 1);
                    assert(expected_min_ops(4, a@, n as int) == 1);
                }
                1
            } else if has3mod4 {
                proof {
                    assert(!has_div4_upto(a@, n as int));
                    assert((cnt_even as int) < 2);
                    assert((cnt_even as int) != 1);
                    lemma_count_even_nonneg(a@, n as int);
                    assert((cnt_even as int) >= 0);
                    assert((cnt_even as int) == 0);
                    assert(cnt_even == 0);
                    assert(count_even_upto(a@, n as int) == 0);
                    assert(has_three_mod4_upto(a@, n as int));
                    assert(min_ops_k4(a@, n as int) == 1);
                    assert(expected_min_ops(4, a@, n as int) == 1);
                }
                1
            } else {
                proof {
                    assert(!has_div4_upto(a@, n as int));
                    assert((cnt_even as int) < 2);
                    assert((cnt_even as int) != 1);
                    lemma_count_even_nonneg(a@, n as int);
                    assert((cnt_even as int) >= 0);
                    assert((cnt_even as int) == 0);
                    assert(cnt_even == 0);
                    assert(count_even_upto(a@, n as int) == 0);
                    assert(!has_three_mod4_upto(a@, n as int));
                    assert(min_ops_k4(a@, n as int) == 2);
                    assert(expected_min_ops(4, a@, n as int) == 2);
                }
                2
            }
        }
    }
}

}
