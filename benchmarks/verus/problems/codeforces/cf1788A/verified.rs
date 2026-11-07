use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_twos_seq(a: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        let add: int = if a[lo] == 2 { 1 } else { 0 };
        add + count_twos_seq(a, lo + 1, hi)
    }
}

pub open spec fn total_twos(a: Seq<i32>, n: int) -> int {
    count_twos_seq(a, 0, n)
}

pub open spec fn split_ok(a: Seq<i32>, n: int, k: int) -> bool {
    1 <= k <= n - 1 && count_twos_seq(a, 0, k) == count_twos_seq(a, k, n)
}

pub open spec fn spec_find(a: Seq<i32>, n: int, target: int, k: int) -> int
    decreases n - k,
{
    if k >= n {
        -1
    } else {
        let pref = count_twos_seq(a, 0, k);
        if k <= n - 1 && pref == target {
            k
        } else {
            spec_find(a, n, target, k + 1)
        }
    }
}

proof fn lemma_count_concat(a: Seq<i32>, lo: int, mid: int, hi: int)
    requires
        lo <= mid <= hi,
    ensures
        count_twos_seq(a, lo, hi) == count_twos_seq(a, lo, mid) + count_twos_seq(a, mid, hi),
    decreases hi - lo,
{
    if lo >= hi {
        assert(lo == mid);
        assert(mid == hi);
    } else if lo == mid {
        assert(count_twos_seq(a, lo, mid) == 0);
        assert(count_twos_seq(a, lo, hi) == count_twos_seq(a, mid, hi));
    } else {
        let add: int = if a[lo] == 2 { 1 } else { 0 };
        assert(lo < mid);
        assert(lo < hi);
        assert(count_twos_seq(a, lo, hi) == add + count_twos_seq(a, lo + 1, hi));
        assert(count_twos_seq(a, lo, mid) == add + count_twos_seq(a, lo + 1, mid));
        lemma_count_concat(a, lo + 1, mid, hi);
        assert(count_twos_seq(a, lo + 1, hi) == count_twos_seq(a, lo + 1, mid) + count_twos_seq(a, mid, hi));
    }
}

proof fn lemma_total_split(a: Seq<i32>, n: int, k: int)
    requires
        0 <= k <= n,
    ensures
        count_twos_seq(a, 0, k) + count_twos_seq(a, k, n) == count_twos_seq(a, 0, n),
{
    lemma_count_concat(a, 0, k, n);
}

proof fn lemma_count_twos_one(a: Seq<i32>, idx: int)
    requires
        0 <= idx < a.len(),
    ensures
        count_twos_seq(a, idx, idx + 1) == (if a[idx] == 2 { 1int } else { 0int }),
{
    reveal_with_fuel(count_twos_seq, 2);
}

proof fn lemma_count_twos_prefix_step(a: Seq<i32>, k: int)
    requires
        k >= 1,
        k <= a.len(),
    ensures
        count_twos_seq(a, 0, k) == count_twos_seq(a, 0, k - 1) + (if a[k - 1] == 2 { 1int } else { 0int }),
{
    assert(0 <= k - 1 < a.len());
    lemma_count_concat(a, 0, k - 1, k);
    lemma_count_twos_one(a, k - 1);
}

proof fn lemma_split_ok_iff_halves(a: Seq<i32>, n: int, k: int)
    requires
        1 <= k <= n - 1,
    ensures
        split_ok(a, n, k) == (count_twos_seq(a, 0, k) * 2 == total_twos(a, n)),
{
    lemma_total_split(a, n, k);
    let left = count_twos_seq(a, 0, k);
    let right = count_twos_seq(a, k, n);
    let t = total_twos(a, n);
    assert(t == left + right);
    assert(split_ok(a, n, k) == (left == right));
    assert((left == right) == (2 * left == t));
}

proof fn lemma_odd_implies_not_split_ok(a: Seq<i32>, n: int, k: int)
    requires
        1 <= k <= n - 1,
        total_twos(a, n) % 2 != 0,
    ensures
        !split_ok(a, n, k),
{
    lemma_split_ok_iff_halves(a, n, k);
    let t = total_twos(a, n);
    let left = count_twos_seq(a, 0, k);
    if split_ok(a, n, k) {
        assert(2 * left == t);
        assert(t % 2 == 0);
        assert(false);
    }
}

proof fn lemma_spec_find_miss(a: Seq<i32>, n: int, target: int, k: int)
    requires
        k < n,
        count_twos_seq(a, 0, k) != target,
    ensures
        spec_find(a, n, target, k) == spec_find(a, n, target, k + 1),
    decreases n - k,
{
    reveal_with_fuel(spec_find, 2);
    let pref = count_twos_seq(a, 0, k);
    assert(pref != target);
    assert(!(k <= n - 1 && pref == target));
}

proof fn lemma_spec_find_hit(a: Seq<i32>, n: int, target: int, k: int)
    requires
        k <= n - 1,
        count_twos_seq(a, 0, k) == target,
    ensures
        spec_find(a, n, target, k) == k,
    decreases n - k,
{
    reveal_with_fuel(spec_find, 2);
    let pref = count_twos_seq(a, 0, k);
    assert(pref == target);
    assert(k <= n - 1 && pref == target);
}

proof fn lemma_spec_find_neg(a: Seq<i32>, n: int, target: int, k: int)
    requires
        k <= n,
        forall|u: int| k <= u <= n - 1 ==> count_twos_seq(a, 0, u) != target,
    ensures
        spec_find(a, n, target, k) == -1,
    decreases n - k,
{
    if k >= n {
        reveal_with_fuel(spec_find, 2);
    } else {
        assert(k <= n - 1);
        assert(count_twos_seq(a, 0, k) != target);
        lemma_spec_find_miss(a, n, target, k);
        assert(forall|u: int| k + 1 <= u <= n - 1 ==> count_twos_seq(a, 0, u) != target);
        lemma_spec_find_neg(a, n, target, k + 1);
    }
}

pub struct Solution;

impl Solution {
    pub fn one_and_two(n: usize, a: Vec<i32>) -> (res: i32)
        requires
            2 <= n <= 1000,
            n == a.len(),
            forall|i: int| 0 <= i < n as int ==> #[trigger] a[i] == 1 || a[i] == 2,
        ensures
            (res == -1) <==> (forall|k: int|
                1 <= k <= n as int - 1 ==> !#[trigger] split_ok(a@, n as int, k)),
            (res >= 1) <==> (exists|k: int|
                1 <= k <= n as int - 1 && #[trigger] split_ok(a@, n as int, k)),
            (res >= 1) <==> (split_ok(a@, n as int, res as int) && forall|j: int|
                1 <= j < res as int ==> !#[trigger] split_ok(a@, n as int, j)),
    {
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == a.len(),
                2 <= n <= 1000,
                forall|u: int| 0 <= u < n as int ==> a[u] == 1 || a[u] == 2,
                total == count_twos_seq(a@, 0, i as int),
                0 <= total <= i as int,
                total <= n as int,
            decreases n - i,
        {
            proof {
                assert(total <= 1000);
                assert((total + 1) <= 1001);
                assert(i < n);
                assert(i < n);
            }
            if a[i] == 2 {
                total = total + 1;
            }
            proof {
                lemma_count_twos_prefix_step(a@, (i + 1) as int);
                assert(total == count_twos_seq(a@, 0, (i + 1) as int));
            }
            i = i + 1;
        }
        proof {
            assert(total == count_twos_seq(a@, 0, n as int));
            assert(total as int == total_twos(a@, n as int));
        }
        if total % 2 != 0 {
            proof {
                assert forall|k: int|
                    (1 <= k <= n as int - 1) implies !split_ok(a@, n as int, k)
                by {
                    lemma_odd_implies_not_split_ok(a@, n as int, k);
                };
            }
            return -1;
        }
        let target: i32 = total / 2;
        let mut twos: i32 = 0;
        let mut k: usize = 1;
        while k < n
            invariant
                n == a.len(),
                2 <= n <= 1000,
                forall|u: int| 0 <= u < n as int ==> a[u] == 1 || a[u] == 2,
                total as int == total_twos(a@, n as int),
                total % 2 == 0,
                target as int == total_twos(a@, n as int) / 2,
                1 <= k <= n,
                twos == count_twos_seq(a@, 0, (k - 1) as int),
                0 <= twos <= (k - 1) as int,
                twos <= n as int,
                spec_find(a@, n as int, target as int, 1) == spec_find(a@, n as int, target as int, k as int),
                forall|u: int|
                    1 <= u < k as int ==> count_twos_seq(a@, 0, u) != target as int,
            decreases n - k,
        {
            proof {
                assert(twos <= 1000);
                assert((twos + 1) <= 1001);
            }
            if a[k - 1] == 2 {
                twos = twos + 1;
            }
            proof {
                assert(k as int <= (a@).len());
                lemma_count_twos_prefix_step(a@, k as int);
                assert(twos == count_twos_seq(a@, 0, k as int));
            }
            if twos == target {
                proof {
                    lemma_spec_find_hit(a@, n as int, target as int, k as int);
                    assert(spec_find(a@, n as int, target as int, k as int) == k as int);
                    assert(spec_find(a@, n as int, target as int, 1) == k as int);
                    let s = a@;
                    lemma_total_split(s, n as int, k as int);
                    assert(count_twos_seq(s, k as int, n as int) == (total_twos(s, n as int) - count_twos_seq(s, 0, k as int)));
                    assert(count_twos_seq(s, 0, k as int) == count_twos_seq(s, k as int, n as int));
                    assert(split_ok(a@, n as int, k as int));
                    assert forall|j: int|
                        1 <= j < k as int implies !split_ok(a@, n as int, j)
                    by {
                        lemma_split_ok_iff_halves(a@, n as int, j);
                        assert(count_twos_seq(a@, 0, j) != target as int);
                        assert(!(count_twos_seq(a@, 0, j) * 2 == total_twos(a@, n as int)));
                        assert(!split_ok(a@, n as int, j));
                    };
                }
                return k as i32;
            }
            proof {
                assert(count_twos_seq(a@, 0, k as int) != target as int);
                lemma_spec_find_miss(a@, n as int, target as int, k as int);
                assert(spec_find(a@, n as int, target as int, k as int)
                    == spec_find(a@, n as int, target as int, (k + 1) as int));
            }
            k = k + 1;
        }
        proof {
            assert(k == n);
            assert(forall|u: int| 1 <= u <= n as int - 1 ==> count_twos_seq(a@, 0, u) != target as int);
            lemma_spec_find_neg(a@, n as int, target as int, 1);
            assert(spec_find(a@, n as int, target as int, 1) == -1);
            assert forall|k2: int|
                (1 <= k2 <= n as int - 1) implies !split_ok(a@, n as int, k2)
            by {
                lemma_split_ok_iff_halves(a@, n as int, k2);
                assert(count_twos_seq(a@, 0, k2) != target as int);
                assert(!(count_twos_seq(a@, 0, k2) * 2 == total_twos(a@, n as int)));
            };
        }
        -1
    }
}

}
