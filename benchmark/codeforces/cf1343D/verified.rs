use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn pair_cost(ai: i64, aj: i64, k: i64, x: i64) -> int {
    if ai + aj == x { 0 }
    else if x >= ({let lo = if ai < aj { ai } else { aj }; lo} + 1) &&
            x <= ({let hi = if ai > aj { ai } else { aj }; hi} + k) { 1 }
    else { 2 }
}

pub open spec fn total_cost_rec(a: Seq<i64>, n: usize, k: i64, x: i64, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else {
        total_cost_rec(a, n, k, x, end - 1)
          + pair_cost(a[end - 1], a[n as int - end], k, x)
    }
}

pub open spec fn total_cost(a: Seq<i64>, n: usize, k: i64, x: i64) -> int {
    total_cost_rec(a, n, k, x, (n / 2) as int)
}

pub open spec fn b2i(b: bool) -> int {
    if b { 1 } else { 0 }
}

pub open spec fn pair_lo(ai: i64, aj: i64) -> i64 {
    if ai < aj { ai } else { aj }
}

pub open spec fn pair_hi(ai: i64, aj: i64) -> i64 {
    if ai > aj { ai } else { aj }
}

pub open spec fn one_change(ai: i64, aj: i64, k: i64, x: i64) -> bool {
    x >= pair_lo(ai, aj) + 1 && x <= pair_hi(ai, aj) + k
}

pub open spec fn cover_count_rec(a: Seq<i64>, n: usize, k: i64, x: i64, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else {
        cover_count_rec(a, n, k, x, end - 1)
            + b2i(one_change(a[end - 1], a[n as int - end], k, x))
    }
}

pub open spec fn exact_count_rec(a: Seq<i64>, n: usize, x: i64, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else {
        exact_count_rec(a, n, x, end - 1)
            + b2i(a[end - 1] + a[n as int - end] == x)
    }
}

pub open spec fn diff_delta_rec(a: Seq<i64>, n: usize, k: i64, pos: i64, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else {
        diff_delta_rec(a, n, k, pos, end - 1)
            + b2i(pair_lo(a[end - 1], a[n as int - end]) + 1 == pos)
            - b2i(pair_hi(a[end - 1], a[n as int - end]) + k + 1 == pos)
    }
}

proof fn lemma_pair_lo_hi_order(ai: i64, aj: i64)
    ensures
        pair_lo(ai, aj) <= pair_hi(ai, aj),
{
}

proof fn lemma_pair_exact_implies_cover(ai: i64, aj: i64, k: i64, x: i64)
    requires
        1 <= ai <= k,
        1 <= aj <= k,
        1 <= k,
        x == ai + aj,
    ensures
        one_change(ai, aj, k, x),
{
    let lo = pair_lo(ai, aj);
    let hi = pair_hi(ai, aj);
    assert(lo <= ai);
    assert(lo <= aj);
    assert(hi >= ai);
    assert(hi >= aj);
    assert(x >= lo + 1) by(nonlinear_arith)
        requires
            x == ai + aj,
            1 <= aj,
            lo <= ai;
    assert(x <= hi + k) by(nonlinear_arith)
        requires
            x == ai + aj,
            aj <= k,
            ai <= hi;
    assert(one_change(ai, aj, k, x));
}

proof fn lemma_pair_cost_formula(ai: i64, aj: i64, k: i64, x: i64)
    requires
        1 <= ai <= k,
        1 <= aj <= k,
        1 <= k,
        2 <= x <= 2 * k,
    ensures
        pair_cost(ai, aj, k, x)
            == 2 - b2i(one_change(ai, aj, k, x)) - b2i(ai + aj == x),
{
    if ai + aj == x {
        lemma_pair_exact_implies_cover(ai, aj, k, x);
        assert(b2i(one_change(ai, aj, k, x)) == 1);
        assert(b2i(ai + aj == x) == 1);
    } else if one_change(ai, aj, k, x) {
        assert(b2i(one_change(ai, aj, k, x)) == 1);
        assert(b2i(ai + aj == x) == 0);
    } else {
        assert(b2i(one_change(ai, aj, k, x)) == 0);
        assert(b2i(ai + aj == x) == 0);
    }
}

proof fn lemma_total_cost_split(a: Seq<i64>, n: usize, k: i64, x: i64, end: int)
    requires
        0 <= end <= (n / 2) as int,
        1 <= k,
        forall|i: int| 0 <= i && i < n ==> 1 <= a[i] && a[i] <= k,
        2 <= x <= 2 * k,
    ensures
        total_cost_rec(a, n, k, x, end)
            == 2 * end - cover_count_rec(a, n, k, x, end) - exact_count_rec(a, n, x, end),
    decreases end
{
    if end > 0 {
        lemma_total_cost_split(a, n, k, x, end - 1);
        let ai = a[end - 1];
        let aj = a[n as int - end];
        lemma_pair_cost_formula(ai, aj, k, x);
    }
}

proof fn lemma_pair_cost_bounds(ai: i64, aj: i64, k: i64, x: i64)
    requires
        1 <= ai <= k,
        1 <= aj <= k,
        1 <= k,
        2 <= x <= 2 * k,
    ensures
        0 <= pair_cost(ai, aj, k, x) <= 2,
{
}

proof fn lemma_cover_count_bounds(a: Seq<i64>, n: usize, k: i64, x: i64, end: int)
    requires
        0 <= end <= (n / 2) as int,
        1 <= k,
        forall|i: int| 0 <= i && i < n ==> 1 <= a[i] && a[i] <= k,
    ensures
        0 <= cover_count_rec(a, n, k, x, end) <= end,
    decreases end
{
    if end > 0 {
        lemma_cover_count_bounds(a, n, k, x, end - 1);
    }
}

proof fn lemma_exact_count_bounds(a: Seq<i64>, n: usize, x: i64, end: int)
    requires
        0 <= end <= (n / 2) as int,
    ensures
        0 <= exact_count_rec(a, n, x, end) <= end,
    decreases end
{
    if end > 0 {
        lemma_exact_count_bounds(a, n, x, end - 1);
    }
}

proof fn lemma_diff_delta_bounds(a: Seq<i64>, n: usize, k: i64, pos: i64, end: int)
    requires
        0 <= end <= (n / 2) as int,
        1 <= k,
        forall|i: int| 0 <= i && i < n ==> 1 <= a[i] && a[i] <= k,
    ensures
        -end <= diff_delta_rec(a, n, k, pos, end) <= end,
    decreases end
{
    if end > 0 {
        lemma_diff_delta_bounds(a, n, k, pos, end - 1);
    }
}

proof fn lemma_total_cost_bounds(a: Seq<i64>, n: usize, k: i64, x: i64, end: int)
    requires
        0 <= end <= (n / 2) as int,
        1 <= k,
        forall|i: int| 0 <= i && i < n ==> 1 <= a[i] && a[i] <= k,
        2 <= x <= 2 * k,
    ensures
        0 <= total_cost_rec(a, n, k, x, end) <= 2 * end,
    decreases end
{
    if end > 0 {
        lemma_total_cost_bounds(a, n, k, x, end - 1);
        lemma_pair_cost_bounds(a[end - 1], a[n as int - end], k, x);
    }
}

proof fn lemma_pair_cover_step(ai: i64, aj: i64, k: i64, x: i64)
    requires
        1 <= ai <= k,
        1 <= aj <= k,
        1 <= k,
        2 <= x <= 2 * k,
    ensures
        b2i(one_change(ai, aj, k, x))
            == b2i(one_change(ai, aj, k, (x - 1) as i64))
                + b2i(pair_lo(ai, aj) + 1 == x)
                - b2i(pair_hi(ai, aj) + k + 1 == x),
{
    let l = pair_lo(ai, aj) + 1;
    let r = pair_hi(ai, aj) + k;
    let r1 = r + 1;
    lemma_pair_lo_hi_order(ai, aj);
    assert(pair_lo(ai, aj) + 1 <= pair_hi(ai, aj) + 1) by(nonlinear_arith)
        requires
            pair_lo(ai, aj) <= pair_hi(ai, aj);
    assert(pair_hi(ai, aj) + 1 <= pair_hi(ai, aj) + k) by(nonlinear_arith)
        requires
            1 <= k;
    assert(l <= r);
    if x == l {
        assert(!one_change(ai, aj, k, (x - 1) as i64));
        assert(one_change(ai, aj, k, x));
        assert(x <= r);
        assert(x < r1) by(nonlinear_arith)
            requires
                x <= r,
                r1 == r + 1;
        assert(r1 != x);
    } else if x == r1 {
        assert(one_change(ai, aj, k, (x - 1) as i64));
        assert(!one_change(ai, aj, k, x));
        assert(l <= r);
        assert(l < x) by(nonlinear_arith)
            requires
                l <= r,
                x == r1,
                r1 == r + 1;
        assert(l != x);
    } else {
        assert((one_change(ai, aj, k, x)) == (one_change(ai, aj, k, (x - 1) as i64))) by {
            if one_change(ai, aj, k, x) {
                assert(l <= x && x <= r);
                assert(x != l);
                assert(l <= x - 1) by(nonlinear_arith)
                    requires
                        l <= x,
                        x != l;
                assert(x - 1 <= r) by(nonlinear_arith)
                    requires
                        x <= r;
                assert(one_change(ai, aj, k, (x - 1) as i64));
            } else if one_change(ai, aj, k, (x - 1) as i64) {
                assert(l <= x - 1 && x - 1 <= r);
                assert(x != r1);
                assert(l <= x) by(nonlinear_arith)
                    requires
                        l <= x - 1;
                assert(x <= r) by(nonlinear_arith)
                    requires
                        x - 1 <= r,
                        x != r + 1;
                assert(one_change(ai, aj, k, x));
            }
        }
    }
}

proof fn lemma_cover_step(a: Seq<i64>, n: usize, k: i64, x: i64, end: int)
    requires
        0 <= end <= (n / 2) as int,
        1 <= k,
        forall|i: int| 0 <= i && i < n ==> 1 <= a[i] && a[i] <= k,
        2 <= x <= 2 * k,
    ensures
        cover_count_rec(a, n, k, x, end)
            == cover_count_rec(a, n, k, (x - 1) as i64, end) + diff_delta_rec(a, n, k, x, end),
    decreases end
{
    if end > 0 {
        lemma_cover_step(a, n, k, x, end - 1);
        lemma_pair_cover_step(a[end - 1], a[n as int - end], k, x);
    }
}

proof fn lemma_cover_at_one_zero(a: Seq<i64>, n: usize, k: i64, end: int)
    requires
        0 <= end <= (n / 2) as int,
        1 <= k,
        forall|i: int| 0 <= i && i < n ==> 1 <= a[i] && a[i] <= k,
    ensures
        cover_count_rec(a, n, k, 1, end) == 0,
    decreases end
{
    if end > 0 {
        lemma_cover_at_one_zero(a, n, k, end - 1);
        let ai = a[end - 1];
        let aj = a[n as int - end];
        assert(pair_lo(ai, aj) + 1 >= 2) by(nonlinear_arith)
            requires
                1 <= ai,
                1 <= aj;
        assert(!one_change(ai, aj, k, 1));
    }
}

pub struct Solution;

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    fn build_tables(n: usize, k: i64, a: &Vec<i64>) -> (res: (Vec<i64>, Vec<i64>))
        requires
            2 <= n && n <= 200000,
            n % 2 == 0,
            1 <= k && k <= 200000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= k,
        ensures
            res.0.len() == (2 * k + 2) as usize,
            res.1.len() == (2 * k + 2) as usize,
            forall|pos: int| 0 <= pos && pos < (2 * k + 2) ==>
                res.0@[pos] as int == diff_delta_rec(a@, n, k, pos as i64, (n / 2) as int),
            forall|pos: int| 0 <= pos && pos < (2 * k + 2) ==>
                res.1@[pos] as int == exact_count_rec(a@, n, pos as i64, (n / 2) as int),
    {
        let half = n / 2;
        let size = (2 * k + 2) as usize;
        let mut diff: Vec<i64> = Vec::new();
        let mut exact: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < size
            invariant
                diff.len() == idx,
                exact.len() == idx,
                idx <= size,
                forall|j: int| 0 <= j && j < idx ==> diff@[j] == 0,
                forall|j: int| 0 <= j && j < idx ==> exact@[j] == 0,
            decreases size - idx
        {
            diff.push(0);
            exact.push(0);
            idx = idx + 1;
        }
        let mut i: usize = 0;
        while i < half
            invariant
                half == n / 2,
                size == (2 * k + 2) as usize,
                0 <= i && i <= half,
                2 <= n && n <= 200000,
                n % 2 == 0,
                1 <= k && k <= 200000,
                a.len() == n,
                diff.len() == size,
                exact.len() == size,
                forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= k,
                forall|pos: int| 0 <= pos && pos < size ==> diff@[pos] as int == diff_delta_rec(a@, n, k, pos as i64, i as int),
                forall|pos: int| 0 <= pos && pos < size ==> exact@[pos] as int == exact_count_rec(a@, n, pos as i64, i as int),
            decreases half - i
        {
            let ai = a[i];
            let aj = a[n - 1 - i];
            let lo = if ai < aj { ai } else { aj };
            let hi = if ai > aj { ai } else { aj };
            let left = (lo + 1) as usize;
            let right_plus_one = (hi + k + 1) as usize;
            let sum = (ai + aj) as usize;
            proof {
                assert(1 <= ai <= k);
                assert(1 <= aj <= k);
                lemma_pair_lo_hi_order(ai, aj);
                assert(2 <= lo + 1);
                assert(lo + 1 <= k + 1);
                assert(k + 2 <= hi + k + 1);
                assert(hi + k + 1 <= 2 * k + 1);
                assert(2 <= ai + aj);
                assert(ai + aj <= 2 * k);
                assert(0 <= left < size);
                assert(0 <= right_plus_one < size);
                assert(0 <= sum < size);
                lemma_diff_delta_bounds(a@, n, k, left as i64, i as int);
                lemma_diff_delta_bounds(a@, n, k, right_plus_one as i64, i as int);
                lemma_exact_count_bounds(a@, n, sum as i64, i as int);
                assert(-(i as int) <= diff@[left as int] as int <= i as int);
                assert(-(i as int) <= diff@[right_plus_one as int] as int <= i as int);
                assert(0 <= exact@[sum as int] as int <= i as int);
            }
            let ghost diff0 = diff@;
            let ghost exact0 = exact@;
            let old_left = diff[left];
            let old_right = diff[right_plus_one];
            let old_sum = exact[sum];
            diff.set(left, diff[left] + 1);
            let ghost diff1 = diff@;
            diff.set(right_plus_one, diff[right_plus_one] - 1);
            exact.set(sum, exact[sum] + 1);
            proof {
                assert(left as int <= hi as int + 1);
                assert(hi as int + 1 < hi as int + k as int + 1) by(nonlinear_arith)
                    requires
                        1 <= k;
                assert((left as int) < (right_plus_one as int));
                assert(left != right_plus_one);
                assert forall|pos: int| 0 <= pos && pos < size implies diff@[pos] as int == diff_delta_rec(a@, n, k, pos as i64, (i + 1) as int) by {
                    if pos == left as int {
                        assert(old_left == diff0[left as int]);
                        assert(diff1[pos] == old_left + 1);
                        assert(diff@[pos] == diff1[pos]);
                        assert(diff_delta_rec(a@, n, k, pos as i64, (i + 1) as int)
                            == diff_delta_rec(a@, n, k, pos as i64, i as int)
                                + 1 - 0);
                    } else if pos == right_plus_one as int {
                        assert(diff1[pos] == diff0[pos]);
                        assert(old_right == diff1[pos]);
                        assert(diff@[pos] == old_right - 1);
                        assert(diff_delta_rec(a@, n, k, pos as i64, (i + 1) as int)
                            == diff_delta_rec(a@, n, k, pos as i64, i as int)
                                + 0 - 1);
                    } else {
                        assert(diff1[pos] == diff0[pos]);
                        assert(diff@[pos] == diff1[pos]);
                        assert(diff_delta_rec(a@, n, k, pos as i64, (i + 1) as int)
                            == diff_delta_rec(a@, n, k, pos as i64, i as int));
                    }
                };
                assert forall|pos: int| 0 <= pos && pos < size implies exact@[pos] as int == exact_count_rec(a@, n, pos as i64, (i + 1) as int) by {
                    if pos == sum as int {
                        assert(old_sum == exact0[sum as int]);
                        assert(exact@[pos] == old_sum + 1);
                        assert(exact_count_rec(a@, n, pos as i64, (i + 1) as int)
                            == exact_count_rec(a@, n, pos as i64, i as int) + 1);
                    } else {
                        assert(exact@[pos] == exact0[pos]);
                        assert(exact_count_rec(a@, n, pos as i64, (i + 1) as int)
                            == exact_count_rec(a@, n, pos as i64, i as int));
                    }
                };
            }
            i = i + 1;
        }
        (diff, exact)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn constant_palindrome_sum(n: usize, k: i64, a: Vec<i64>) -> (ans: i64)
        requires
            2 <= n && n <= 200000,
            n % 2 == 0,
            1 <= k && k <= 200000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= k,
        ensures
            0 <= ans && ans <= n as i64,
            forall|x: i64| 2 <= x && x <= 2 * k ==>
                ans as int <= total_cost(a@, n, k, x),
            exists|x: i64| 2 <= x && x <= 2 * k && ans as int == total_cost(a@, n, k, x),
    {
        let tables = Solution::build_tables(n, k, &a);
        let diff = tables.0;
        let exact = tables.1;
        let mut ans = n as i64;
        let ghost mut best_x: i64 = 0;
        let mut cover: i64 = 0;
        let mut x: usize = 2;
        let limit = (2 * k) as usize;
        proof {
            lemma_cover_at_one_zero(a@, n, k, (n / 2) as int);
            assert(cover_count_rec(a@, n, k, 1, (n / 2) as int) == 0);
        }
        while x <= limit
            invariant
                limit == (2 * k) as usize,
                diff.len() == (2 * k + 2) as usize,
                exact.len() == (2 * k + 2) as usize,
                forall|pos: int| 0 <= pos && pos < (2 * k + 2) ==> diff@[pos] as int == diff_delta_rec(a@, n, k, pos as i64, (n / 2) as int),
                forall|pos: int| 0 <= pos && pos < (2 * k + 2) ==> exact@[pos] as int == exact_count_rec(a@, n, pos as i64, (n / 2) as int),
                2 <= n && n <= 200000,
                n % 2 == 0,
                1 <= k && k <= 200000,
                a.len() == n,
                forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= k,
                2 <= x && x <= limit + 1,
                0 <= ans && ans <= n as i64,
                cover as int == cover_count_rec(a@, n, k, (x - 1) as i64, (n / 2) as int),
                forall|y: i64| 2 <= y && y < x as i64 ==> ans as int <= total_cost(a@, n, k, y),
                best_x == 0 ==> (x == 2 && ans == n as i64),
                best_x != 0 ==> (2 <= best_x && best_x <= 2 * k
                    && ans as int == total_cost(a@, n, k, best_x)),
            decreases limit + 1 - x
        {
            proof {
                lemma_cover_step(a@, n, k, x as i64, (n / 2) as int);
                lemma_cover_count_bounds(a@, n, k, (x - 1) as i64, (n / 2) as int);
                lemma_diff_delta_bounds(a@, n, k, x as i64, (n / 2) as int);
                assert(diff@[x as int] as int == diff_delta_rec(a@, n, k, x as i64, (n / 2) as int));
                assert(-((n / 2) as int) <= diff@[x as int] as int <= (n / 2) as int);
                assert(-200000 <= cover as int + diff@[x as int] as int <= 200000) by(nonlinear_arith)
                    requires
                        0 <= cover as int <= (n / 2) as int,
                        -((n / 2) as int) <= diff@[x as int] as int <= (n / 2) as int,
                        n <= 200000;
                assert(cover as int + diff@[x as int] as int == cover_count_rec(a@, n, k, x as i64, (n / 2) as int));
            }
            cover = cover + diff[x];
            proof {
                assert(cover as int == cover_count_rec(a@, n, k, x as i64, (n / 2) as int));
                lemma_cover_count_bounds(a@, n, k, x as i64, (n / 2) as int);
                lemma_exact_count_bounds(a@, n, x as i64, (n / 2) as int);
                assert(exact@[x as int] as int == exact_count_rec(a@, n, x as i64, (n / 2) as int));
                assert(0 <= exact@[x as int] as int <= (n / 2) as int);
                assert(0 <= n as int - cover as int - exact@[x as int] as int <= n as int) by(nonlinear_arith)
                    requires
                        0 <= cover as int <= (n / 2) as int,
                        0 <= exact@[x as int] as int <= (n / 2) as int,
                        n % 2 == 0;
            }
            let cost = n as i64 - cover - exact[x];
            proof {
                lemma_total_cost_split(a@, n, k, x as i64, (n / 2) as int);
                lemma_total_cost_bounds(a@, n, k, x as i64, (n / 2) as int);
                assert(cost as int == n as int - cover as int - exact@[x as int] as int);
                assert(cost as int == total_cost(a@, n, k, x as i64));
                assert(0 <= cost <= n as i64);
            }
            let ghost ans_before = ans;
            if cost < ans {
                ans = cost;
            }
            proof {
                if best_x == 0 || cost < ans_before {
                    best_x = x as i64;
                }
            }
            proof {
                assert(ans as int <= total_cost(a@, n, k, x as i64));
                assert forall|y: i64| 2 <= y && y < (x + 1) as i64 implies ans as int <= total_cost(a@, n, k, y) by {
                    if y < x as i64 {
                    } else {
                        assert(y == x as i64);
                    }
                };
            }
            x = x + 1;
        }
        proof {
            assert(x == limit + 1);
            assert(limit == (2 * k) as usize);
            assert forall|y: i64| 2 <= y && y <= 2 * k implies ans as int <= total_cost(a@, n, k, y) by {
                assert(y < x as i64);
            };
            assert(limit >= 2);
            assert(best_x != 0);
            assert(2 <= best_x && best_x <= 2 * k && ans as int == total_cost(a@, n, k, best_x));
            assert(exists|xx: i64| 2 <= xx && xx <= 2 * k && ans as int == total_cost(a@, n, k, xx));
        }
        ans
    }
}

}
