use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn perm_fn(n: int, i: int) -> int {
    if i % 2 == 0 { i / 2 } else { n / 2 + (i - 1) / 2 }
}

pub open spec fn iterate_perm(n: int, start: int, steps: nat) -> int
    decreases steps,
{
    if steps == 0 {
        start
    } else {
        perm_fn(n, iterate_perm(n, start, (steps - 1) as nat))
    }
}

spec fn count_in_range(vals: Seq<int>, lo: int, hi: int) -> int
    decreases vals.len(),
{
    if vals.len() == 0 {
        0
    } else {
        (if lo <= vals.last() < hi { 1int } else { 0int })
            + count_in_range(vals.drop_last(), lo, hi)
    }
}

spec fn filter_range(vals: Seq<int>, lo: int, hi: int) -> Seq<int>
    decreases vals.len(),
{
    if vals.len() == 0 {
        Seq::<int>::empty()
    } else {
        let rest = filter_range(vals.drop_last(), lo, hi);
        if lo <= vals.last() < hi {
            rest.push(vals.last())
        } else {
            rest
        }
    }
}

proof fn perm_fn_preserves_range(n: int, i: int)
    requires
        n >= 4,
        n % 2 == 0,
        1 <= i <= n - 2,
    ensures
        1 <= perm_fn(n, i) <= n - 2,
{
}

proof fn iterate_perm_range(n: int, k: nat)
    requires
        n >= 4,
        n % 2 == 0,
    ensures
        1 <= iterate_perm(n, 1, (k + 1) as nat) <= n - 2,
    decreases k,
{
    reveal_with_fuel(iterate_perm, 2);
    if k == 0 {
        perm_fn_preserves_range(n, 1);
    } else {
        iterate_perm_range(n, (k - 1) as nat);
        perm_fn_preserves_range(n, iterate_perm(n, 1, k as nat));
    }
}

proof fn iterate_perm_range_gen(n: int, start: int, k: nat)
    requires
        n >= 4,
        n % 2 == 0,
        1 <= start <= n - 2,
    ensures
        1 <= iterate_perm(n, start, (k + 1) as nat) <= n - 2,
    decreases k,
{
    reveal_with_fuel(iterate_perm, 2);
    if k == 0 {
        perm_fn_preserves_range(n, start);
    } else {
        iterate_perm_range_gen(n, start, (k - 1) as nat);
        perm_fn_preserves_range(n, iterate_perm(n, start, k as nat));
    }
}

proof fn perm_fn_injective(n: int, a: int, b: int)
    requires
        n >= 4,
        n % 2 == 0,
        1 <= a <= n - 2,
        1 <= b <= n - 2,
        perm_fn(n, a) == perm_fn(n, b),
    ensures
        a == b,
{
    if a % 2 == 0 && b % 2 == 0 {
    } else if a % 2 != 0 && b % 2 != 0 {
    } else if a % 2 == 0 && b % 2 != 0 {
        assert(a / 2 == n / 2 + (b - 1) / 2);
        assert(a / 2 <= (n - 2) / 2);
        assert(n / 2 + (b - 1) / 2 >= n / 2);
        assert(false);
    } else {
        assert(n / 2 + (a - 1) / 2 == b / 2);
        assert(n / 2 + (a - 1) / 2 >= n / 2);
        assert(b / 2 <= (n - 2) / 2);
        assert(false);
    }
}

proof fn iterate_perm_compose(n: int, x: int, a: nat, b: nat)
    ensures
        iterate_perm(n, x, (a + b) as nat) == iterate_perm(n, iterate_perm(n, x, a), b),
    decreases b,
{
    if b == 0 {
    } else {
        iterate_perm_compose(n, x, a, (b - 1) as nat);
    }
}

proof fn iterate_perm_injective(n: int, a: int, b: int, k: nat)
    requires
        n >= 4,
        n % 2 == 0,
        1 <= a <= n - 2,
        1 <= b <= n - 2,
        iterate_perm(n, a, k) == iterate_perm(n, b, k),
    ensures
        a == b,
    decreases k,
{
    reveal_with_fuel(iterate_perm, 2);
    if k == 0 {
    } else if k == 1 {
        perm_fn_injective(n, a, b);
    } else {
        iterate_perm_range_gen(n, a, (k - 2) as nat);
        iterate_perm_range_gen(n, b, (k - 2) as nat);
        perm_fn_injective(
            n,
            iterate_perm(n, a, (k - 1) as nat),
            iterate_perm(n, b, (k - 1) as nat),
        );
        iterate_perm_injective(n, a, b, (k - 1) as nat);
    }
}

proof fn cycle_return(n: int, i: nat, j: nat)
    requires
        n >= 4,
        n % 2 == 0,
        i < j,
        iterate_perm(n, 1, i) == iterate_perm(n, 1, j),
    ensures
        iterate_perm(n, 1, (j - i) as nat) == 1,
{
    iterate_perm_compose(n, 1, (j - i) as nat, i);
    if i == 0 {
    } else {
        let a = iterate_perm(n, 1, (j - i) as nat);
        iterate_perm_range(n, (i - 1) as nat);
        iterate_perm_range(n, (j - 1) as nat);
        if j - i >= 1 {
            iterate_perm_range(n, (j - i - 1) as nat);
        }
        iterate_perm_injective(n, a, 1, i);
    }
}

proof fn count_partition(vals: Seq<int>, lo: int, mid: int, hi: int)
    requires
        lo <= mid <= hi,
        forall |i: int| 0 <= i < vals.len() ==> lo <= #[trigger] vals[i] < hi,
    ensures
        count_in_range(vals, lo, mid) + count_in_range(vals, mid, hi)
            == vals.len(),
    decreases vals.len(),
{
    if vals.len() > 0 {
        count_partition(vals.drop_last(), lo, mid, hi);
    }
}

proof fn filter_len(vals: Seq<int>, lo: int, hi: int)
    ensures
        filter_range(vals, lo, hi).len() == count_in_range(vals, lo, hi),
    decreases vals.len(),
{
    if vals.len() > 0 {
        filter_len(vals.drop_last(), lo, hi);
    }
}

proof fn filter_bounds(vals: Seq<int>, lo: int, hi: int)
    ensures
        forall |i: int| 0 <= i < filter_range(vals, lo, hi).len()
            ==> lo <= #[trigger] filter_range(vals, lo, hi)[i] < hi,
    decreases vals.len(),
{
    if vals.len() > 0 {
        filter_bounds(vals.drop_last(), lo, hi);
        let rest = filter_range(vals.drop_last(), lo, hi);
        if lo <= vals.last() < hi {
            assert forall |i: int| 0 <= i < rest.push(vals.last()).len()
                implies lo <= #[trigger] rest.push(vals.last())[i] < hi by {
                if i < rest.len() {
                    assert(lo <= rest[i] < hi);
                } else {
                    assert(rest.push(vals.last())[i] == vals.last());
                }
            };
        }
    }
}

proof fn filter_elements_from(vals: Seq<int>, lo: int, hi: int)
    ensures
        forall |fi: int| 0 <= fi < filter_range(vals, lo, hi).len()
            ==> exists |oi: int|
                0 <= oi < vals.len()
                    && vals[oi] == #[trigger] filter_range(vals, lo, hi)[fi],
    decreases vals.len(),
{
    if vals.len() > 0 {
        filter_elements_from(vals.drop_last(), lo, hi);
        let rest = filter_range(vals.drop_last(), lo, hi);
        if lo <= vals.last() < hi {
            assert forall |fi: int|
                0 <= fi < rest.push(vals.last()).len()
            implies exists |oi: int|
                0 <= oi < vals.len()
                    && vals[oi]
                        == #[trigger] rest.push(vals.last())[fi]
            by {
                if fi < rest.len() {
                    let oi = choose |oi: int|
                        0 <= oi < vals.drop_last().len()
                            && vals.drop_last()[oi] == rest[fi];
                    assert(vals[oi] == rest.push(vals.last())[fi]);
                } else {
                    assert(vals[vals.len() - 1]
                        == rest.push(vals.last())[fi]);
                }
            };
        }
    }
}

proof fn filter_no_dups(vals: Seq<int>, lo: int, hi: int)
    requires
        forall |i: int, j: int|
            0 <= i < j < vals.len() ==> #[trigger] vals[i] != #[trigger] vals[j],
    ensures
        forall |i: int, j: int|
            0 <= i < j < filter_range(vals, lo, hi).len()
                ==> #[trigger] filter_range(vals, lo, hi)[i]
                    != #[trigger] filter_range(vals, lo, hi)[j],
    decreases vals.len(),
{
    if vals.len() > 0 {
        let prefix = vals.drop_last();
        assert forall |i: int, j: int|
            0 <= i < j < prefix.len()
        implies #[trigger] prefix[i] != #[trigger] prefix[j] by {
            assert(vals[i] != vals[j]);
        };
        filter_no_dups(prefix, lo, hi);

        let rest = filter_range(prefix, lo, hi);
        if lo <= vals.last() < hi {
            filter_elements_from(prefix, lo, hi);
            assert forall |i: int|
                0 <= i < rest.len()
            implies vals.last() != #[trigger] rest[i] by {
                let oi = choose |oi: int|
                    0 <= oi < prefix.len() && prefix[oi] == rest[i];
                assert(vals[oi] != vals[vals.len() - 1]);
            };
            assert forall |i: int, j: int|
                0 <= i < j < rest.push(vals.last()).len()
            implies #[trigger] rest.push(vals.last())[i]
                != #[trigger] rest.push(vals.last())[j]
            by {
                if j < rest.len() {
                    assert(rest[i] != rest[j]);
                } else {
                    assert(rest[i] != vals.last());
                }
            };
        }
    }
}

proof fn distinct_bounded(vals: Seq<int>, lo: int, hi: int)
    requires
        hi > lo,
        vals.len() as int > hi - lo,
        forall |i: int| 0 <= i < vals.len()
            ==> lo <= #[trigger] vals[i] < hi,
        forall |i: int, j: int|
            0 <= i < j < vals.len()
                ==> #[trigger] vals[i] != #[trigger] vals[j],
    ensures
        false,
    decreases hi - lo,
{
    if hi == lo + 1 {
        assert(vals.len() >= 2);
        assert(vals[0] == lo);
        assert(vals[1] == lo);
        assert(vals[0] != vals[1]);
    } else {
        let mid = lo + (hi - lo) / 2;
        let c_lo = count_in_range(vals, lo, mid);
        let c_hi = count_in_range(vals, mid, hi);
        count_partition(vals, lo, mid, hi);

        if c_lo > mid - lo {
            let f = filter_range(vals, lo, mid);
            filter_len(vals, lo, mid);
            filter_bounds(vals, lo, mid);
            filter_no_dups(vals, lo, mid);
            distinct_bounded(f, lo, mid);
        } else {
            assert(c_hi > hi - mid);
            let f = filter_range(vals, mid, hi);
            filter_len(vals, mid, hi);
            filter_bounds(vals, mid, hi);
            filter_no_dups(vals, mid, hi);
            distinct_bounded(f, mid, hi);
        }
    }
}

proof fn cycle_bound(n: int, ops: int)
    requires
        n >= 4,
        n % 2 == 0,
        ops >= 1,
        ops <= n - 2,
        forall |k: int| 1 <= k <= ops
            ==> #[trigger] iterate_perm(n, 1, k as nat) != 1,
    ensures
        ops < n - 2,
{
    if ops == n - 2 {
        let vals = Seq::new(
            (n - 2) as nat,
            |k: int| iterate_perm(n, 1, (k + 1) as nat),
        );
        assert forall |i: int|
            0 <= i < vals.len()
        implies 2 <= #[trigger] vals[i] <= n - 2 by {
            iterate_perm_range(n, i as nat);
            assert(iterate_perm(n, 1, (i + 1) as nat) != 1);
        };
        assert forall |i: int|
            0 <= i < vals.len()
        implies 2 <= #[trigger] vals[i] < n - 1 by {};
        assert forall |i: int, j: int|
            0 <= i < j < vals.len()
        implies #[trigger] vals[i] != #[trigger] vals[j] by {
            if vals[i] == vals[j] {
                cycle_return(n, (i + 1) as nat, (j + 1) as nat);
                assert(iterate_perm(n, 1, (j - i) as nat) == 1);
                assert(1 <= j - i <= n - 3);
                assert(iterate_perm(n, 1, (j - i) as nat) != 1);
            }
        };
        distinct_bounded(vals, 2, n - 1);
    }
}

impl Solution {
    pub fn reinitialize_permutation(n: i32) -> (res: i32)
        requires
            2 <= n <= 1000,
            n % 2 == 0,
        ensures
            res >= 1,
            iterate_perm(n as int, 1, res as nat) == 1,
            forall |k: int| 1 <= k < res
                ==> #[trigger] iterate_perm(n as int, 1, k as nat) != 1,
    {
        if n == 2 {
            proof {
                reveal_with_fuel(iterate_perm, 2);
            }
            return 1;
        }
        let mut val: i32 = n / 2;
        let mut ops: i32 = 1;

        proof {
            reveal_with_fuel(iterate_perm, 2);
            perm_fn_preserves_range(n as int, 1);
        }

        while val != 1
            invariant
                4 <= n <= 1000,
                n % 2 == 0,
                1 <= val <= n - 2,
                1 <= ops <= n - 2,
                val == iterate_perm(n as int, 1int, ops as nat),
                forall |k: int| 1 <= k < ops
                    ==> #[trigger] iterate_perm(n as int, 1int, k as nat)
                        != 1,
            decreases n - 2 - ops,
        {
            proof {
                reveal_with_fuel(iterate_perm, 2);
                assert(val != 1);
                assert(iterate_perm(n as int, 1, ops as nat) != 1);
                cycle_bound(n as int, ops as int);
                perm_fn_preserves_range(n as int, val as int);
            }
            if val % 2 == 0 {
                val = val / 2;
            } else {
                val = n / 2 + (val - 1) / 2;
            }
            ops = ops + 1;
        }
        ops
    }
}

}
