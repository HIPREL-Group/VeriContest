use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_value(n: int, k: int) -> int {
    k * (6 * n - 1)
}

pub open spec fn gcd_pos(a: int, b: int) -> int
    recommends
        a > 0 && b > 0,
    decreases a + b when a > 0 && b > 0
{
    if a == b {
        a
    } else if a > b {
        gcd_pos(a - b, b)
    } else {
        gcd_pos(a, b - a)
    }
}

pub open spec fn row_rank_k(s: Seq<i32>, kk: int) -> bool {
    &&& s.len() == 4
    &&& s[0] != s[1]
    &&& s[0] != s[2]
    &&& s[0] != s[3]
    &&& s[1] != s[2]
    &&& s[1] != s[3]
    &&& s[2] != s[3]
    &&& forall |i: int, j: int|
        0 <= i && i < j && j < 4 ==> gcd_pos(s[i] as int, s[j] as int) == kk
}

pub open spec fn col_offset(c: int) -> int {
    if c == 0 { 1 }
    else if c == 1 { 2 }
    else if c == 2 { 3 }
    else { 5 }
}

proof fn lemma_gcd_one(a: int)
    requires a > 0,
    ensures gcd_pos(a, 1) == 1,
    decreases a,
{
    if a == 1 {
    } else {
        lemma_gcd_one(a - 1);
    }
}

proof fn lemma_gcd_two(a: int)
    requires a > 0, a % 2 == 1,
    ensures gcd_pos(a, 2) == 1,
    decreases a,
{
    if a == 1 {
        reveal_with_fuel(gcd_pos, 3);
    } else {
        lemma_gcd_two(a - 2);
    }
}

proof fn lemma_gcd_three(a: int)
    requires a > 0, a % 3 != 0,
    ensures gcd_pos(a, 3) == 1,
    decreases a,
{
    if a == 1 {
        reveal_with_fuel(gcd_pos, 4);
    } else if a == 2 {
        reveal_with_fuel(gcd_pos, 4);
    } else {
        lemma_gcd_three(a - 3);
    }
}

proof fn lemma_gcd_four(a: int)
    requires a > 0, a % 2 == 1,
    ensures gcd_pos(a, 4) == 1,
    decreases a,
{
    if a == 1 {
        reveal_with_fuel(gcd_pos, 5);
    } else if a == 3 {
        reveal_with_fuel(gcd_pos, 5);
    } else {
        lemma_gcd_four(a - 4);
    }
}

proof fn lemma_gcd_scale(kk: int, a: int, b: int)
    requires kk > 0, a > 0, b > 0,
    ensures gcd_pos(kk * a, kk * b) == kk * gcd_pos(a, b),
    decreases a + b,
{
    assert(kk * a > 0) by(nonlinear_arith) requires kk > 0, a > 0;
    assert(kk * b > 0) by(nonlinear_arith) requires kk > 0, b > 0;
    if a == b {
    } else if a > b {
        assert(kk * a > kk * b) by(nonlinear_arith)
            requires kk > 0, a > b;
        assert(kk * a - kk * b == kk * (a - b)) by(nonlinear_arith)
            requires kk > 0;
        lemma_gcd_scale(kk, a - b, b);
    } else {
        assert(kk * b > kk * a) by(nonlinear_arith)
            requires kk > 0, b > a;
        assert(kk * b - kk * a == kk * (b - a)) by(nonlinear_arith)
            requires kk > 0;
        lemma_gcd_scale(kk, a, b - a);
    }
}

proof fn lemma_row_gcd(ii: int, kk: int)
    requires ii >= 0, kk > 0,
    ensures
        gcd_pos(kk * (6 * ii + 1), kk * (6 * ii + 2)) == kk,
        gcd_pos(kk * (6 * ii + 1), kk * (6 * ii + 3)) == kk,
        gcd_pos(kk * (6 * ii + 1), kk * (6 * ii + 5)) == kk,
        gcd_pos(kk * (6 * ii + 2), kk * (6 * ii + 3)) == kk,
        gcd_pos(kk * (6 * ii + 2), kk * (6 * ii + 5)) == kk,
        gcd_pos(kk * (6 * ii + 3), kk * (6 * ii + 5)) == kk,
{
    assert((6 * ii + 1) % 2 == 1) by(nonlinear_arith) requires ii >= 0;
    assert((6 * ii + 2) % 3 != 0) by(nonlinear_arith) requires ii >= 0;
    assert((6 * ii + 3) % 2 == 1) by(nonlinear_arith) requires ii >= 0;

    lemma_gcd_scale(kk, 6 * ii + 1, 6 * ii + 2);
    lemma_gcd_one(6 * ii + 1);
    assert(gcd_pos(6 * ii + 1, 6 * ii + 2) == 1);

    lemma_gcd_scale(kk, 6 * ii + 1, 6 * ii + 3);
    lemma_gcd_two(6 * ii + 1);
    assert(gcd_pos(6 * ii + 1, 6 * ii + 3) == 1);

    lemma_gcd_scale(kk, 6 * ii + 1, 6 * ii + 5);
    lemma_gcd_four(6 * ii + 1);
    assert(gcd_pos(6 * ii + 1, 6 * ii + 5) == 1);

    lemma_gcd_scale(kk, 6 * ii + 2, 6 * ii + 3);
    lemma_gcd_one(6 * ii + 2);
    assert(gcd_pos(6 * ii + 2, 6 * ii + 3) == 1);

    lemma_gcd_scale(kk, 6 * ii + 2, 6 * ii + 5);
    lemma_gcd_three(6 * ii + 2);
    assert(gcd_pos(6 * ii + 2, 6 * ii + 5) == 1);

    lemma_gcd_scale(kk, 6 * ii + 3, 6 * ii + 5);
    lemma_gcd_two(6 * ii + 3);
    assert(gcd_pos(6 * ii + 3, 6 * ii + 5) == 1);
}

impl Solution {
    pub fn build_dreamoon_sets(n: usize, k: i32) -> (sets: Vec<Vec<i32>>)
        requires
            1 <= n <= 10000,
            1 <= k <= 100,
        ensures
            sets@.len() == n as int,
            forall |r: int| 0 <= r < n as int ==> #[trigger] row_rank_k(sets@[r]@, k as int),
            forall |r: int, c: int|
                0 <= r < n as int && 0 <= c < 4 ==>
                    1 <= (#[trigger] sets@[r]@[c] as int)
                    && (sets@[r]@[c] as int) <= max_value(n as int, k as int),
            forall |r1: int, c1: int, r2: int, c2: int|
                #![trigger sets@[r1]@[c1], sets@[r2]@[c2]]
                0 <= r1 < n as int && 0 <= c1 < 4 && 0 <= r2 < n as int && 0 <= c2 < 4
                    && (r1 != r2 || c1 != c2)
                    ==> sets@[r1]@[c1] != sets@[r2]@[c2],
    {
        let mut sets: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n <= 10000,
                1 <= k <= 100,
                sets@.len() == i as int,
                forall |r: int| 0 <= r < i as int ==> #[trigger] sets@[r]@.len() == 4,
                forall |r: int, c: int| 0 <= r < i as int && 0 <= c < 4 ==>
                    (#[trigger] sets@[r]@[c] as int) == (k as int) * (6 * r + col_offset(c)),
                forall |r: int| 0 <= r < i as int ==> #[trigger] row_rank_k(sets@[r]@, k as int),
            decreases n - i,
        {
            proof {
                
                assert(i < 10000);
                assert(6 * (i as int) + 5 <= 6 * 9999 + 5) by (nonlinear_arith)
                    requires i < 10000;
                assert(0 < (k as int) * (6 * (i as int) + 5) < 2147483647) by (nonlinear_arith)
                    requires 1 <= k <= 100, i < 10000;
            }

            let base = 6 * (i as i64);
            proof {
                assert(0 < (k as i64) * (base + 1) < 2147483647) by (nonlinear_arith)
                    requires 1 <= k <= 100, i < 10000, base == 6 * (i as i64);
                assert(0 < (k as i64) * (base + 2) < 2147483647) by (nonlinear_arith)
                    requires 1 <= k <= 100, i < 10000, base == 6 * (i as i64);
                assert(0 < (k as i64) * (base + 3) < 2147483647) by (nonlinear_arith)
                    requires 1 <= k <= 100, i < 10000, base == 6 * (i as i64);
                assert(0 < (k as i64) * (base + 5) < 2147483647) by (nonlinear_arith)
                    requires 1 <= k <= 100, i < 10000, base == 6 * (i as i64);
            }
            let v0 = ((k as i64) * (base + 1)) as i32;
            let v1 = ((k as i64) * (base + 2)) as i32;
            let v2 = ((k as i64) * (base + 3)) as i32;
            let v3 = ((k as i64) * (base + 5)) as i32;

            let mut row: Vec<i32> = Vec::new();
            row.push(v0);
            row.push(v1);
            row.push(v2);
            row.push(v3);

            proof {
                assert(row@.len() == 4);
                assert(row@[0] as int == (k as int) * (6 * (i as int) + col_offset(0)));
                assert(row@[1] as int == (k as int) * (6 * (i as int) + col_offset(1)));
                assert(row@[2] as int == (k as int) * (6 * (i as int) + col_offset(2)));
                assert(row@[3] as int == (k as int) * (6 * (i as int) + col_offset(3)));
                assert((k as int) * (6 * (i as int) + col_offset(0)) < (k as int) * (6 * (i as int) + col_offset(1))) by (nonlinear_arith)
                    requires 1 <= k;
                assert((k as int) * (6 * (i as int) + col_offset(1)) < (k as int) * (6 * (i as int) + col_offset(2))) by (nonlinear_arith)
                    requires 1 <= k;
                assert((k as int) * (6 * (i as int) + col_offset(2)) < (k as int) * (6 * (i as int) + col_offset(3))) by (nonlinear_arith)
                    requires 1 <= k;
                assert((row@[0] as int) < (row@[1] as int));
                assert((row@[1] as int) < (row@[2] as int));
                assert((row@[2] as int) < (row@[3] as int));
                assert(row@[0] != row@[1]);
                assert(row@[0] != row@[2]);
                assert(row@[0] != row@[3]);
                assert(row@[1] != row@[2]);
                assert(row@[1] != row@[3]);
                assert(row@[2] != row@[3]);
                lemma_row_gcd(i as int, k as int);
                assert(row_rank_k(row@, k as int));
            }
            sets.push(row);
            i = i + 1;
        }
        
        proof {
            assert forall |r: int, c: int|
                0 <= r < n as int && 0 <= c < 4
            implies
                1 <= (#[trigger] sets@[r]@[c] as int)
                && (sets@[r]@[c] as int) <= max_value(n as int, k as int)
            by {
                assert(sets@[r]@[c] as int == (k as int) * (6 * r + col_offset(c)));
                assert(col_offset(c) >= 1);
                assert(col_offset(c) <= 5);
                assert(6 * r + col_offset(c) >= 1);
                assert(6 * r + col_offset(c) <= 6 * (n as int - 1) + 5);
                assert(1 <= (k as int) * (6 * r + col_offset(c))) by(nonlinear_arith)
                    requires k as int >= 1, 6 * r + col_offset(c) >= 1;
                assert((k as int) * (6 * r + col_offset(c)) <= (k as int) * (6 * (n as int) - 1)) by(nonlinear_arith)
                    requires k as int >= 1, 6 * r + col_offset(c) >= 1, 6 * r + col_offset(c) <= 6 * (n as int) - 1;
            };

            assert forall |r1: int, c1: int, r2: int, c2: int|
                #![trigger sets@[r1]@[c1], sets@[r2]@[c2]]
                0 <= r1 < n as int && 0 <= c1 < 4 && 0 <= r2 < n as int && 0 <= c2 < 4
                    && (r1 != r2 || c1 != c2)
            implies
                sets@[r1]@[c1] != sets@[r2]@[c2]
            by {
                assert(sets@[r1]@[c1] as int == (k as int) * (6 * r1 + col_offset(c1)));
                assert(sets@[r2]@[c2] as int == (k as int) * (6 * r2 + col_offset(c2)));
                if r1 == r2 {
                    assert(col_offset(c1) != col_offset(c2));
                } else if r1 < r2 {
                    assert(col_offset(c1) <= 5);
                    assert(col_offset(c2) >= 1);
                    assert(6 * r1 + 5 < 6 * r2 + 1);
                } else {
                    assert(col_offset(c2) <= 5);
                    assert(col_offset(c1) >= 1);
                    assert(6 * r2 + 5 < 6 * r1 + 1);
                }
                assert(6 * r1 + col_offset(c1) != 6 * r2 + col_offset(c2));
                assert((k as int) * (6 * r1 + col_offset(c1)) != (k as int) * (6 * r2 + col_offset(c2))) by(nonlinear_arith)
                    requires k as int >= 1, 6 * r1 + col_offset(c1) != 6 * r2 + col_offset(c2);
            };
        }
        sets
    }
}
}