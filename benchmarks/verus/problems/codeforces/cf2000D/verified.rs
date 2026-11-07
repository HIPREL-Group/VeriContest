use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pref_sum(a: Seq<i64>, idx: int) -> int
    recommends
        0 <= idx <= a.len(),
    decreases idx,
{
    if idx <= 0 {
        0int
    } else {
        pref_sum(a, idx - 1) + a[idx - 1] as int
    }
}

pub open spec fn leftmost_l(s: Seq<u8>, lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi <= s.len(),
    decreases if hi > lo { hi - lo } else { 0int },
{
    if lo >= hi {
        -1int
    } else if s[lo] == 1u8 {
        lo
    } else {
        leftmost_l(s, lo + 1, hi)
    }
}

pub open spec fn rightmost_r(s: Seq<u8>, lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi <= s.len(),
    decreases if hi > lo { hi - lo } else { 0int },
{
    if lo >= hi {
        -1int
    } else if s[hi - 1] == 2u8 {
        hi - 1
    } else {
        rightmost_r(s, lo, hi - 1)
    }
}


proof fn lemma_leftmost_l_bounds(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        leftmost_l(s, lo, hi) == -1int || (lo <= leftmost_l(s, lo, hi) < hi),
    decreases if hi > lo { hi - lo } else { 0int },
{
    if lo >= hi {
    } else if s[lo] == 1u8 {
    } else {
        lemma_leftmost_l_bounds(s, lo + 1, hi);
    }
}

proof fn lemma_rightmost_r_bounds(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        rightmost_r(s, lo, hi) == -1int || (lo <= rightmost_r(s, lo, hi) < hi),
    decreases if hi > lo { hi - lo } else { 0int },
{
    if lo >= hi {
    } else if s[hi - 1] == 2u8 {
    } else {
        lemma_rightmost_r_bounds(s, lo, hi - 1);
    }
}

pub open spec fn greedy(a: Seq<i64>, s: Seq<u8>, lo: int, hi: int) -> int
    recommends
        a.len() == s.len(),
        0 <= lo <= hi <= a.len(),
    decreases if hi > lo { hi - lo } else { 0int },
    when 0 <= lo <= hi <= s.len()
    via greedy_decreases
{
    let l = leftmost_l(s, lo, hi);
    let r = rightmost_r(s, lo, hi);
    if l < 0 || r < 0 || l >= r {
        0int
    } else {
        (pref_sum(a, r + 1) - pref_sum(a, l)) + greedy(a, s, l + 1, r)
    }
}

#[via_fn]
proof fn greedy_decreases(a: Seq<i64>, s: Seq<u8>, lo: int, hi: int)
{
    lemma_leftmost_l_bounds(s, lo, hi);
    lemma_rightmost_r_bounds(s, lo, hi);
}


proof fn lemma_leftmost_l_skip(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo < hi <= s.len(),
        s[lo] != 1u8,
    ensures
        leftmost_l(s, lo, hi) == leftmost_l(s, lo + 1, hi),
{
    reveal_with_fuel(leftmost_l, 2);
}


proof fn lemma_greedy_skip_l(a: Seq<i64>, s: Seq<u8>, lo: int, hi: int)
    requires
        a.len() == s.len(),
        0 <= lo < hi <= a.len(),
        s[lo] != 1u8,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 1u8 || s[i] == 2u8,
    ensures
        greedy(a, s, lo, hi) == greedy(a, s, lo + 1, hi),
{
    reveal_with_fuel(greedy, 2);
    reveal_with_fuel(leftmost_l, 2);
    let l1 = leftmost_l(s, lo, hi);
    let l2 = leftmost_l(s, lo + 1, hi);
    assert(l1 == l2);
    let r1 = rightmost_r(s, lo, hi);
    let r2 = rightmost_r(s, lo + 1, hi);
    lemma_leftmost_l_neg(s, lo + 1, hi);
    if r2 >= 0 {
        lemma_rightmost_r_unaffected_by_lo(s, lo, hi);
        assert(r1 == r2);
        if l1 < 0 || r1 < 0 || l1 >= r1 {
            assert(greedy(a, s, lo, hi) == 0int);
            assert(greedy(a, s, lo + 1, hi) == 0int);
        } else {
        }
    } else {
        lemma_rightmost_r_neg(s, lo + 1, hi);
        assert(r2 == -1int);
        if s[lo] == 2u8 {
            lemma_rightmost_r_eq_lo(s, lo, hi);
            assert(r1 == lo);
            
            assert(greedy(a, s, lo + 1, hi) == 0int);
            
            if l1 < 0 {
                assert(greedy(a, s, lo, hi) == 0int);
            } else {
                
                assert(l1 >= lo + 1);
                assert(l1 > r1);
                assert(greedy(a, s, lo, hi) == 0int);
            }
        } else {
            assert(false);
        }
    }
}

proof fn lemma_rightmost_r_unaffected_by_lo(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo < hi <= s.len(),
        rightmost_r(s, lo + 1, hi) >= 0,
    ensures
        rightmost_r(s, lo, hi) == rightmost_r(s, lo + 1, hi),
    decreases hi - lo,
{
    if hi == lo + 1 {
        
        reveal_with_fuel(rightmost_r, 1);
    } else {
        reveal_with_fuel(rightmost_r, 2);
        if s[hi - 1] == 2u8 {
            assert(rightmost_r(s, lo, hi) == hi - 1);
            assert(rightmost_r(s, lo + 1, hi) == hi - 1);
        } else {
            lemma_rightmost_r_unaffected_by_lo(s, lo, hi - 1);
        }
    }
}

proof fn lemma_rightmost_r_eq_lo(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo < hi <= s.len(),
        s[lo] == 2u8,
        rightmost_r(s, lo + 1, hi) == -1int,
    ensures
        rightmost_r(s, lo, hi) == lo,
    decreases hi - lo,
{
    if hi == lo + 1 {
        reveal_with_fuel(rightmost_r, 1);
        assert(rightmost_r(s, lo, hi) == lo);
    } else {
        reveal_with_fuel(rightmost_r, 2);
        
        if s[hi - 1] == 2u8 {
            
            assert(rightmost_r(s, lo + 1, hi) == hi - 1);
            assert(false);
        }
        lemma_rightmost_r_eq_lo(s, lo, hi - 1);
    }
}


proof fn lemma_greedy_skip_r(a: Seq<i64>, s: Seq<u8>, lo: int, hi: int)
    requires
        a.len() == s.len(),
        0 <= lo < hi <= a.len(),
        s[hi - 1] != 2u8,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 1u8 || s[i] == 2u8,
    ensures
        greedy(a, s, lo, hi) == greedy(a, s, lo, hi - 1),
{
    reveal_with_fuel(greedy, 2);
    reveal_with_fuel(rightmost_r, 2);
    let l1 = leftmost_l(s, lo, hi);
    let l2 = leftmost_l(s, lo, hi - 1);
    let r1 = rightmost_r(s, lo, hi);
    let r2 = rightmost_r(s, lo, hi - 1);
    assert(r1 == r2);
    lemma_rightmost_r_neg(s, lo, hi - 1);
    if l2 >= 0 {
        lemma_leftmost_l_unaffected_by_hi(s, lo, hi);
        assert(l1 == l2);
        
        if l1 < 0 || r1 < 0 || l1 >= r1 {
            assert(greedy(a, s, lo, hi) == 0int);
            assert(greedy(a, s, lo, hi - 1) == 0int);
        } else {
            assert(greedy(a, s, lo, hi) == (pref_sum(a, r1 + 1) - pref_sum(a, l1)) + greedy(a, s, l1 + 1, r1));
            assert(greedy(a, s, lo, hi - 1) == (pref_sum(a, r2 + 1) - pref_sum(a, l2)) + greedy(a, s, l2 + 1, r2));
        }
    } else {
        lemma_leftmost_l_neg(s, lo, hi - 1);
        assert(l2 == -1int);
        if s[hi - 1] == 1u8 {
            lemma_leftmost_l_eq_hi_minus_1(s, lo, hi);
            assert(l1 == hi - 1);
            
            assert(greedy(a, s, lo, hi - 1) == 0int);
            
            if r1 < 0 {
                assert(greedy(a, s, lo, hi) == 0int);
            } else {
                
                assert(r1 < hi - 1);
                assert(l1 >= r1);
                assert(greedy(a, s, lo, hi) == 0int);
            }
        } else {
            assert(s[hi - 1] == 1u8 || s[hi - 1] == 2u8);
            assert(false);
        }
    }
}

proof fn lemma_leftmost_l_neg(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        leftmost_l(s, lo, hi) == -1int || (lo <= leftmost_l(s, lo, hi) < hi),
    decreases if hi > lo { hi - lo } else { 0int },
{
    if lo >= hi {
    } else if s[lo] == 1u8 {
    } else {
        lemma_leftmost_l_neg(s, lo + 1, hi);
    }
}

proof fn lemma_rightmost_r_neg(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
    ensures
        rightmost_r(s, lo, hi) == -1int || (lo <= rightmost_r(s, lo, hi) < hi),
    decreases if hi > lo { hi - lo } else { 0int },
{
    if lo >= hi {
    } else if s[hi - 1] == 2u8 {
    } else {
        lemma_rightmost_r_neg(s, lo, hi - 1);
    }
}

proof fn lemma_leftmost_l_unaffected_by_hi(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo < hi <= s.len(),
        leftmost_l(s, lo, hi - 1) >= 0,
    ensures
        leftmost_l(s, lo, hi) == leftmost_l(s, lo, hi - 1),
    decreases hi - lo,
{
    if hi - 1 == lo {
        reveal_with_fuel(leftmost_l, 1);
    } else {
        reveal_with_fuel(leftmost_l, 2);
        if s[lo] == 1u8 {
            assert(leftmost_l(s, lo, hi) == lo);
            assert(leftmost_l(s, lo, hi - 1) == lo);
        } else {
            lemma_leftmost_l_unaffected_by_hi(s, lo + 1, hi);
        }
    }
}

proof fn lemma_leftmost_l_eq_hi_minus_1(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo < hi <= s.len(),
        s[hi - 1] == 1u8,
        leftmost_l(s, lo, hi - 1) == -1int,
    ensures
        leftmost_l(s, lo, hi) == hi - 1,
    decreases hi - lo,
{
    if hi - 1 == lo {
        reveal_with_fuel(leftmost_l, 2);
    } else {
        reveal_with_fuel(leftmost_l, 2);
        if s[lo] == 1u8 {
            assert(leftmost_l(s, lo, hi - 1) == lo);
            assert(false);
        }
        lemma_leftmost_l_eq_hi_minus_1(s, lo + 1, hi);
    }
}


proof fn lemma_greedy_zero(a: Seq<i64>, s: Seq<u8>, lo: int, hi: int)
    requires
        a.len() == s.len(),
        0 <= lo <= hi <= a.len(),
        hi <= lo + 1,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 1u8 || s[i] == 2u8,
    ensures
        greedy(a, s, lo, hi) == 0int,
{
    reveal_with_fuel(greedy, 1);
    if lo >= hi {
        reveal_with_fuel(leftmost_l, 1);
        reveal_with_fuel(rightmost_r, 1);
        assert(leftmost_l(s, lo, hi) == -1int);
        assert(rightmost_r(s, lo, hi) == -1int);
    } else {
        
        assert(s[lo] == 1u8 || s[lo] == 2u8);
        if s[lo] == 1u8 {
            reveal_with_fuel(leftmost_l, 1);
            assert(leftmost_l(s, lo, hi) == lo);
            reveal_with_fuel(rightmost_r, 2);
            
            reveal_with_fuel(rightmost_r, 1);
            assert(rightmost_r(s, lo, lo) == -1int);
            assert(rightmost_r(s, lo, hi) == -1int);
        } else {
            assert(s[lo] == 2u8);
            reveal_with_fuel(leftmost_l, 2);
            
            reveal_with_fuel(leftmost_l, 1);
            assert(leftmost_l(s, lo + 1, lo + 1) == -1int);
            assert(leftmost_l(s, lo, hi) == -1int);
            reveal_with_fuel(rightmost_r, 1);
            assert(rightmost_r(s, lo, hi) == lo);
        }
    }
}


proof fn lemma_rightmost_r_skip(s: Seq<u8>, lo: int, hi: int)
    requires
        0 <= lo < hi <= s.len(),
        s[hi - 1] != 2u8,
    ensures
        rightmost_r(s, lo, hi) == rightmost_r(s, lo, hi - 1),
{
    reveal_with_fuel(rightmost_r, 2);
}












proof fn lemma_pref_sum_bound(a: Seq<i64>, idx: int)
    requires
        0 <= idx <= a.len(),
        a.len() <= 200_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 100_000,
    ensures
        0 <= pref_sum(a, idx) <= idx * 100_000,
    decreases idx,
{
    if idx <= 0 {
    } else {
        lemma_pref_sum_bound(a, idx - 1);
        assert(1 <= a[idx - 1] <= 100_000);
    }
}


proof fn lemma_pref_sum_monotonic(a: Seq<i64>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= a.len(),
        a.len() <= 200_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 100_000,
    ensures
        pref_sum(a, hi) >= pref_sum(a, lo),
        pref_sum(a, hi) - pref_sum(a, lo) <= (hi - lo) * 100_000,
    decreases hi - lo,
{
    if hi == lo {
    } else {
        lemma_pref_sum_monotonic(a, lo, hi - 1);
        assert(1 <= a[hi - 1] <= 100_000);
    }
}


proof fn lemma_prefix_step(a: Seq<i64>, prefix: Seq<i64>, i: int)
    requires
        0 <= i < a.len(),
        prefix.len() == i + 1,
        forall|j: int| 0 <= j <= i ==> #[trigger] prefix[j] as int == pref_sum(a, j),
    ensures
        prefix[i] as int + a[i] as int == pref_sum(a, i + 1),
{
    reveal_with_fuel(pref_sum, 2);
}

impl Solution {
    pub fn max_score(a: Vec<i64>, s: Vec<u8>) -> (result: i64)
        requires
            2 <= a.len() <= 200_000,
            a.len() == s.len(),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 100_000,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 1u8 || s[i] == 2u8,
        ensures
            result as int == greedy(a@, s@, 0, a.len() as int),
    {
        let n = a.len();
        let ghost na = a@;
        let ghost ns = s@;
        
        let mut prefix: Vec<i64> = Vec::with_capacity(n + 1);
        prefix.push(0);
        proof {
            assert(prefix[0] as int == pref_sum(a@, 0));
        }
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                a.len() <= 200_000,
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 100_000,
                prefix.len() == i + 1,
                forall|j: int| 0 <= j <= i as int ==> #[trigger] prefix[j] as int == pref_sum(a@, j),
                forall|j: int| 0 <= j <= i as int ==> 0 <= #[trigger] prefix[j] <= j * 100_000,
            decreases n - i,
        {
            proof {
                lemma_pref_sum_bound(a@, i as int);
                lemma_pref_sum_bound(a@, (i + 1) as int);
                lemma_prefix_step(a@, prefix@, i as int);
                assert((i + 1) as int * 100_000 <= 200_000 * 100_000) by(nonlinear_arith) requires (i + 1) as int <= 200_000;
            }
            let next = prefix[i] + a[i];
            prefix.push(next);
            i = i + 1;
        }
        
        let mut total: i64 = 0;
        let mut lo: usize = 0;
        let mut hi: usize = n;
        let mut keep_going: bool = true;
        while keep_going
            invariant
                0 <= lo <= hi <= n,
                n == a.len(),
                a.len() == s.len(),
                a.len() <= 200_000,
                a.len() >= 2,
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 100_000,
                forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] == 1u8 || s[j] == 2u8,
                prefix.len() == n + 1,
                forall|j: int| 0 <= j <= n as int ==> #[trigger] prefix[j] as int == pref_sum(a@, j),
                forall|j: int| 0 <= j <= n as int ==> 0 <= #[trigger] prefix[j] <= j * 100_000,
                total as int + greedy(a@, s@, lo as int, hi as int) == greedy(a@, s@, 0, n as int),
                0 <= total as int,
                2 * (total as int) <= ((lo as int) + ((n as int) - (hi as int))) * (n as int) * 100_000,
                !keep_going ==> hi <= lo + 1 && total as int == greedy(a@, s@, 0, n as int),
            decreases hi - lo + (if keep_going { 1int } else { 0int }),
        {
            
            let ghost orig_lo = lo;
            let ghost orig_hi_outer = hi;
            let ghost orig_total = total;
            while lo < hi && s[lo] != 1
                invariant
                    orig_lo <= lo <= hi <= n,
                    hi == orig_hi_outer,
                    total == orig_total,
                    n == s.len(),
                    a.len() == s.len(),
                    forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] == 1u8 || s[j] == 2u8,
                    leftmost_l(s@, orig_lo as int, hi as int) == leftmost_l(s@, lo as int, hi as int),
                    greedy(a@, s@, orig_lo as int, hi as int) == greedy(a@, s@, lo as int, hi as int),
                    2 * (total as int) <= ((lo as int) + ((n as int) - (hi as int))) * (n as int) * 100_000,
                decreases hi - lo,
            {
                proof {
                    lemma_leftmost_l_skip(s@, lo as int, hi as int);
                    lemma_greedy_skip_l(a@, s@, lo as int, hi as int);
                    
                    let cur_pos = (lo as int) + ((n as int) - (hi as int));
                    let new_pos = ((lo as int) + 1) + ((n as int) - (hi as int));
                    assert(new_pos == cur_pos + 1);
                    assert(new_pos * (n as int) * 100_000 >= cur_pos * (n as int) * 100_000) by(nonlinear_arith)
                        requires new_pos == cur_pos + 1, n as int >= 0;
                }
                lo = lo + 1;
            }
            proof {
                
                if lo == hi {
                    
                    reveal_with_fuel(leftmost_l, 1);
                    assert(leftmost_l(s@, lo as int, hi as int) == -1int);
                } else {
                    assert(s@[lo as int] == 1u8);
                    reveal_with_fuel(leftmost_l, 1);
                    assert(leftmost_l(s@, lo as int, hi as int) == lo as int);
                }
                assert(leftmost_l(s@, orig_lo as int, hi as int) == leftmost_l(s@, lo as int, hi as int));
            }
            
            let ghost orig_hi = hi;
            let ghost orig_lo_2 = lo;
            let ghost orig_total_2 = total;
            while lo < hi && s[hi - 1] != 2
                invariant
                    lo <= hi <= orig_hi <= n,
                    lo == orig_lo_2,
                    total == orig_total_2,
                    n == s.len(),
                    a.len() == s.len(),
                    forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] == 1u8 || s[j] == 2u8,
                    rightmost_r(s@, lo as int, orig_hi as int) == rightmost_r(s@, lo as int, hi as int),
                    greedy(a@, s@, lo as int, orig_hi as int) == greedy(a@, s@, lo as int, hi as int),
                    2 * (total as int) <= ((lo as int) + ((n as int) - (hi as int))) * (n as int) * 100_000,
                decreases hi,
            {
                proof {
                    lemma_rightmost_r_skip(s@, lo as int, hi as int);
                    lemma_greedy_skip_r(a@, s@, lo as int, hi as int);
                    let cur_pos = (lo as int) + ((n as int) - (hi as int));
                    let new_pos = (lo as int) + ((n as int) - ((hi as int) - 1));
                    assert(new_pos == cur_pos + 1);
                    assert(new_pos * (n as int) * 100_000 >= cur_pos * (n as int) * 100_000) by(nonlinear_arith)
                        requires new_pos == cur_pos + 1, n as int >= 0;
                }
                hi = hi - 1;
            }
            proof {
                if lo == hi {
                    
                    reveal_with_fuel(rightmost_r, 1);
                    assert(rightmost_r(s@, lo as int, hi as int) == -1int);
                } else {
                    assert(s@[(hi - 1) as int] == 2u8);
                    reveal_with_fuel(rightmost_r, 1);
                    assert(rightmost_r(s@, lo as int, hi as int) == (hi - 1) as int);
                }
                assert(rightmost_r(s@, lo as int, orig_hi as int) == rightmost_r(s@, lo as int, hi as int));
            }
            
            if lo + 1 < hi {
                let ghost old_lo = lo;
                let ghost old_hi = hi;
                let ghost old_total = total;
                proof {
                    reveal_with_fuel(greedy, 2);
                    let l = leftmost_l(s@, lo as int, hi as int);
                    let r = rightmost_r(s@, lo as int, hi as int);
                    assert(l == lo as int);
                    assert(r == (hi - 1) as int);
                    assert(l < r);
                    assert(greedy(a@, s@, lo as int, hi as int) ==
                        (pref_sum(a@, r + 1) - pref_sum(a@, l)) + greedy(a@, s@, l + 1, r));
                    assert(prefix[hi as int] as int == pref_sum(a@, hi as int));
                    assert(prefix[lo as int] as int == pref_sum(a@, lo as int));
                    assert(prefix[hi as int] <= hi as int * 100_000);
                    assert((hi as int) * 100_000 <= 200_000 * 100_000) by(nonlinear_arith) requires hi as int <= 200_000;
                    assert(prefix[lo as int] >= 0);
                    
                    
                    assert(2 * (total as int) <= ((lo as int) + ((n as int) - (hi as int))) * (n as int) * 100_000);
                    assert((lo as int) + ((n as int) - (hi as int)) <= (n as int)) by(nonlinear_arith)
                        requires lo as int <= hi as int, hi as int <= n as int;
                    assert(((lo as int) + ((n as int) - (hi as int))) * (n as int) <= (n as int) * (n as int)) by(nonlinear_arith)
                        requires (lo as int) + ((n as int) - (hi as int)) <= (n as int), n as int >= 0;
                    assert((n as int) * (n as int) <= 200_000 * 200_000) by(nonlinear_arith) requires n as int <= 200_000;
                    assert(2 * (total as int) <= 200_000 * 200_000 * 100_000);
                    assert(total as int <= 100_000 * 200_000 * 200_000);
                    assert(total as int + prefix[hi as int] as int <= 100_000 * 200_000 * 200_000 + 200_000 * 100_000);
                }
                total = total + prefix[hi] - prefix[lo];
                lo = lo + 1;
                hi = hi - 1;
                proof {
                    assert(total as int == old_total as int + prefix[old_hi as int] as int - prefix[old_lo as int] as int);
                    assert(prefix[old_hi as int] as int == pref_sum(a@, old_hi as int));
                    assert(prefix[old_lo as int] as int == pref_sum(a@, old_lo as int));
                    lemma_pref_sum_monotonic(a@, old_lo as int, old_hi as int);
                    assert(pref_sum(a@, old_hi as int) >= pref_sum(a@, old_lo as int));
                    assert(0 <= total as int);
                    assert(pref_sum(a@, old_hi as int) - pref_sum(a@, old_lo as int) <= (old_hi as int - old_lo as int) * 100_000);
                    assert((old_hi as int - old_lo as int) * 100_000 <= (n as int) * 100_000) by(nonlinear_arith)
                        requires old_hi as int - old_lo as int <= n as int;
                    let old_pos = (old_lo as int) + (n as int) - (old_hi as int);
                    let new_pos = (lo as int) + (n as int) - (hi as int);
                    assert(new_pos == old_pos + 2);
                    assert(2 * (total as int) == 2 * (old_total as int) + 2 * (prefix[old_hi as int] as int - prefix[old_lo as int] as int));
                    assert(2 * (old_total as int) <= old_pos * (n as int) * 100_000);
                    assert(2 * (total as int) <= old_pos * (n as int) * 100_000 + 2 * (n as int) * 100_000);
                    assert((old_pos + 2) * (n as int) * 100_000 == old_pos * (n as int) * 100_000 + 2 * (n as int) * 100_000) by(nonlinear_arith);
                    assert(2 * (total as int) <= new_pos * (n as int) * 100_000);
                    
                    reveal_with_fuel(greedy, 2);
                    let l = leftmost_l(s@, old_lo as int, old_hi as int);
                    let r = rightmost_r(s@, old_lo as int, old_hi as int);
                    assert(l == old_lo as int);
                    assert(r == (old_hi - 1) as int);
                    assert(l < r);
                    assert(greedy(a@, s@, old_lo as int, old_hi as int) ==
                        (pref_sum(a@, r + 1) - pref_sum(a@, l)) + greedy(a@, s@, l + 1, r));
                    assert(greedy(a@, s@, old_lo as int, old_hi as int) ==
                        (pref_sum(a@, old_hi as int) - pref_sum(a@, old_lo as int)) + greedy(a@, s@, old_lo as int + 1, old_hi as int - 1));
                    assert(lo as int == old_lo as int + 1);
                    assert(hi as int == old_hi as int - 1);
                    assert(greedy(a@, s@, lo as int, hi as int) == greedy(a@, s@, old_lo as int + 1, old_hi as int - 1));
                    
                    
                    
                    
                    
                }
            } else {
                proof {
                    assert(hi <= lo + 1);
                    lemma_greedy_zero(a@, s@, lo as int, hi as int);
                    assert(greedy(a@, s@, lo as int, hi as int) == 0int);
                }
                keep_going = false;
            }
        }
        proof {
            assert(!keep_going);
            assert(total as int == greedy(a@, s@, 0, n as int));
        }
        total
    }
}

}
