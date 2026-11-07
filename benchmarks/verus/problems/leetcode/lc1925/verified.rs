use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_square_triple(a: int, b: int, c: int) -> bool {
    a * a + b * b == c * c
}

pub open spec fn sq_val(c: int) -> int { c * c }

pub open spec fn count_for_c(n: int, a: int, b: int, c: int) -> int
    decreases n - c + 1,
{
    if c > n {
        0
    } else {
        (if is_square_triple(a, b, c) { 1int } else { 0int }) + count_for_c(n, a, b, c + 1)
    }
}

pub open spec fn count_for_b(n: int, a: int, b: int) -> int
    decreases n - b + 1,
{
    if b > n {
        0
    } else {
        count_for_c(n, a, b, 1) + count_for_b(n, a, b + 1)
    }
}

pub open spec fn count_for_a(n: int, a: int) -> int
    decreases n - a + 1,
{
    if a > n {
        0
    } else {
        count_for_b(n, a, 1) + count_for_a(n, a + 1)
    }
}

proof fn square_strict_mono(c1: int, c2: int)
    requires
        c1 >= 1,
        c2 > c1,
    ensures
        c2 * c2 > c1 * c1,
{
    assert(c2 * c2 - c1 * c1 == (c2 - c1) * (c2 + c1)) by(nonlinear_arith);
    assert((c2 - c1) * (c2 + c1) > 0) by(nonlinear_arith)
        requires c2 - c1 > 0, c2 + c1 > 0;
}

proof fn count_for_c_zero_no_match(n: int, a: int, b: int, c: int, witness: int)
    requires
        n >= 1,
        c >= 1,
        witness >= 1,
        witness < c,
        is_square_triple(a, b, witness),
    ensures
        count_for_c(n, a, b, c) == 0,
    decreases n - c + 1,
{
    if c > n {
    } else {
        square_strict_mono(witness, c);
        assert(!is_square_triple(a, b, c));
        count_for_c_zero_no_match(n, a, b, c + 1, witness);
    }
}

proof fn count_for_c_at_most_one(n: int, a: int, b: int, c: int)
    requires
        n >= 1,
        c >= 1,
    ensures
        count_for_c(n, a, b, c) <= 1,
    decreases n - c + 1,
{
    if c > n {
    } else {
        count_for_c_at_most_one(n, a, b, c + 1);
        if is_square_triple(a, b, c) {
            count_for_c_zero_no_match(n, a, b, c + 1, c);
        } else {
            count_for_c_bound(n, a, b, c + 1);
        }
    }
}

proof fn count_for_c_has_match(n: int, a: int, b: int, c: int, target: int)
    requires
        n >= 1,
        1 <= c <= target,
        target <= n,
        is_square_triple(a, b, target),
    ensures
        count_for_c(n, a, b, c) >= 1,
    decreases target - c,
{
    count_for_c_bound(n, a, b, c + 1);
    if c == target {
    } else {
        count_for_c_has_match(n, a, b, c + 1, target);
    }
}

proof fn count_for_c_no_match(n: int, a: int, b: int, c: int)
    requires
        n >= 1,
        c >= 1,
        forall|c_: int| c <= c_ <= n ==> !is_square_triple(a, b, c_),
    ensures
        count_for_c(n, a, b, c) == 0,
    decreases n - c + 1,
{
    if c > n {
    } else {
        count_for_c_no_match(n, a, b, c + 1);
    }
}

proof fn count_for_c_with_is_sq(n: int, a: int, b: int, is_sq: Seq<bool>)
    requires
        n >= 1,
        a >= 1,
        b >= 1,
        a <= n,
        b <= n,
        is_sq.len() == n * n + 1,
        forall|v: int| 0 <= v <= n * n ==>
            (#[trigger] is_sq[v] == (exists|c_: int| 1 <= c_ <= n && #[trigger] sq_val(c_) == v)),
    ensures
        count_for_c(n, a, b, 1) == (
            if a * a + b * b <= n * n && is_sq[a * a + b * b] { 1int } else { 0int }
        ),
{
    let s = a * a + b * b;
    assert(a * a >= 1) by(nonlinear_arith) requires a >= 1;
    assert(b * b >= 1) by(nonlinear_arith) requires b >= 1;

    if s <= n * n && is_sq[s] {
        let c_ = choose|c_: int| 1 <= c_ <= n && sq_val(c_) == s;
        count_for_c_has_match(n, a, b, 1, c_);
        count_for_c_at_most_one(n, a, b, 1);
    } else {
        if s <= n * n {
            assert(!is_sq[s]);
            assert(!(exists|c_: int| 1 <= c_ <= n && sq_val(c_) == s));
            assert forall|c_: int| 1 <= c_ <= n implies !is_square_triple(a, b, c_) by {
                if is_square_triple(a, b, c_) {
                    assert(sq_val(c_) == s);
                    assert(1 <= c_ <= n && sq_val(c_) == s);
                }
            }
            count_for_c_no_match(n, a, b, 1);
        } else {
            assert(s > n * n);
            assert forall|c_: int| 1 <= c_ <= n implies !is_square_triple(a, b, c_) by {
                if is_square_triple(a, b, c_) {
                    assert(sq_val(c_) == s);
                    assert(c_ * c_ <= n * n) by(nonlinear_arith) requires 1 <= c_ <= n;
                    assert(false);
                }
            }
            count_for_c_no_match(n, a, b, 1);
        }
    }
}

proof fn count_for_c_bound(n: int, a: int, b: int, c: int)
    requires
        n >= 1,
    ensures
        count_for_c(n, a, b, c) >= 0,
        1 <= c <= n + 1 ==> count_for_c(n, a, b, c) <= n - c + 1,
    decreases n - c + 1,
{
    if c > n {
    } else {
        count_for_c_bound(n, a, b, c + 1);
    }
}

proof fn count_for_b_bound(n: int, a: int, b: int)
    requires
        n >= 1,
    ensures
        count_for_b(n, a, b) >= 0,
        1 <= b <= n + 1 ==> count_for_b(n, a, b) <= n * (n - b + 1),
    decreases n - b + 1,
{
    if b > n {
    } else {
        count_for_b_bound(n, a, b + 1);
        count_for_c_bound(n, a, b, 1);
        assert(n + n * (n - b) == n * (n - b + 1)) by (nonlinear_arith);
    }
}

proof fn count_for_a_bound(n: int, a: int)
    requires
        n >= 1,
    ensures
        count_for_a(n, a) >= 0,
        1 <= a <= n + 1 ==> count_for_a(n, a) <= n * n * (n - a + 1),
    decreases n - a + 1,
{
    if a > n {
    } else {
        count_for_a_bound(n, a + 1);
        count_for_b_bound(n, a, 1);
        assert(n * n + n * n * (n - a) == n * n * (n - a + 1)) by (nonlinear_arith);
    }
}

impl Solution {
    pub fn count_triples(n: i32) -> (result: i32)
        requires
            1 <= n <= 250,
        ensures
            result == count_for_a(n as int, 1),
    {
        proof {
            count_for_a_bound(n as int, 1);
            assert((n as int) * (n as int) * (n as int) <= 250 * 250 * 250) by (nonlinear_arith)
                requires 1 <= n <= 250;
            assert((n as int) * (n as int) <= 250 * 250) by(nonlinear_arith)
                requires 1 <= n <= 250;
        }

        let max_sq: i32 = n * n;

        let mut is_sq: Vec<bool> = Vec::new();
        let mut idx: i32 = 0;
        while idx <= max_sq
            invariant
                1 <= n <= 250,
                max_sq == n * n,
                0 <= max_sq <= 62500,
                0 <= idx <= max_sq + 1,
                is_sq@.len() == idx as int,
                forall|v: int| 0 <= v < idx as int ==> #[trigger] is_sq@[v] == false,
            decreases max_sq - idx + 1,
        {
            is_sq.push(false);
            idx = idx + 1;
        }

        let mut c: i32 = 1;
        while c <= n
            invariant
                1 <= n <= 250,
                max_sq == n * n,
                0 <= max_sq <= 62500,
                1 <= c <= n + 1,
                is_sq@.len() == max_sq as int + 1,
                forall|v: int| 0 <= v <= max_sq as int ==>
                    (#[trigger] is_sq@[v] == (exists|c_: int| 1 <= c_ < c as int && #[trigger] sq_val(c_) == v)),
            decreases n - c + 1,
        {
            proof {
                assert((c as int) * (c as int) <= max_sq as int) by(nonlinear_arith)
                    requires 1 <= c <= n, max_sq == (n as int) * (n as int);
                assert((c as int) * (c as int) >= 0) by(nonlinear_arith)
                    requires c >= 1;
            }
            is_sq.set((c * c) as usize, true);
            proof {
                assert forall|v: int| 0 <= v <= max_sq as int implies
                    #[trigger] is_sq@[v] == (exists|c_: int| 1 <= c_ < (c as int) + 1 && #[trigger] sq_val(c_) == v)
                by {
                    if v == (c as int) * (c as int) {
                        assert(is_sq@[v] == true);
                        assert(sq_val(c as int) == v);
                    } else {
                        assert(is_sq@[v] == (exists|c_: int| 1 <= c_ < c as int && #[trigger] sq_val(c_) == v));
                        assert((exists|c_: int| 1 <= c_ < c as int && #[trigger] sq_val(c_) == v)
                            == (exists|c_: int| 1 <= c_ < (c as int) + 1 && #[trigger] sq_val(c_) == v)) by {
                            if exists|c_: int| 1 <= c_ < (c as int) + 1 && #[trigger] sq_val(c_) == v {
                                let c_ = choose|c_: int| 1 <= c_ < (c as int) + 1 && #[trigger] sq_val(c_) == v;
                                if c_ == c as int {
                                    assert(c_ * c_ == (c as int) * (c as int));
                                    assert(v == (c as int) * (c as int));
                                    assert(false);
                                }
                                assert(c_ < c as int);
                            }
                        }
                    }
                }
            }
            c = c + 1;
        }

        proof {
            assert forall|v: int| 0 <= v <= max_sq as int implies
                #[trigger] is_sq@[v] == (exists|c_: int| 1 <= c_ <= n as int && #[trigger] sq_val(c_) == v)
            by {
                assert(is_sq@[v] == (exists|c_: int| 1 <= c_ < (n as int + 1) && #[trigger] sq_val(c_) == v));
            }
        }

        let mut count: i32 = 0;
        let mut a: i32 = 1;
        while a <= n
            invariant
                1 <= n <= 250,
                max_sq == n * n,
                0 <= max_sq <= 62500,
                1 <= a <= n + 1,
                is_sq@.len() == max_sq as int + 1,
                forall|v: int| 0 <= v <= max_sq as int ==>
                    (#[trigger] is_sq@[v] == (exists|c_: int| 1 <= c_ <= n as int && #[trigger] sq_val(c_) == v)),
                count as int + count_for_a(n as int, a as int) == count_for_a(n as int, 1),
                count_for_a(n as int, a as int) >= 0,
                count_for_a(n as int, 1) <= 250 * 250 * 250,
                0 <= count,
            decreases
                n - a + 1,
        {
            proof {
                count_for_a_bound(n as int, (a + 1) as int);
                count_for_b_bound(n as int, a as int, 1);
            }
            let mut b: i32 = 1;
            while b <= n
                invariant
                    1 <= n <= 250,
                    max_sq == n * n,
                    0 <= max_sq <= 62500,
                    1 <= a <= n,
                    1 <= b <= n + 1,
                    is_sq@.len() == max_sq as int + 1,
                    forall|v: int| 0 <= v <= max_sq as int ==>
                        (#[trigger] is_sq@[v] == (exists|c_: int| 1 <= c_ <= n as int && #[trigger] sq_val(c_) == v)),
                    count as int + count_for_b(n as int, a as int, b as int)
                        + count_for_a(n as int, (a + 1) as int)
                        == count_for_a(n as int, 1),
                    count_for_b(n as int, a as int, b as int) >= 0,
                    count_for_a(n as int, (a + 1) as int) >= 0,
                    count_for_a(n as int, 1) <= 250 * 250 * 250,
                    0 <= count,
                decreases
                    n - b + 1,
            {
                proof {
                    count_for_b_bound(n as int, a as int, (b + 1) as int);
                    count_for_c_bound(n as int, a as int, b as int, 1);
                    assert((a as int) * (a as int) <= 250 * 250) by (nonlinear_arith)
                        requires 1 <= a <= 250;
                    assert((b as int) * (b as int) <= 250 * 250) by (nonlinear_arith)
                        requires 1 <= b <= 250;
                }
                let s: i32 = a * a + b * b;
                proof {
                    count_for_c_with_is_sq(n as int, a as int, b as int, is_sq@);
                }
                if s <= max_sq && is_sq[s as usize] {
                    count = count + 1;
                }
                b = b + 1;
            }
            a = a + 1;
        }
        count
    }
}

}
