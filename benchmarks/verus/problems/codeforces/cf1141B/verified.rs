use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn circ_rest_segment(a: Seq<i32>, n: int, start: int, len: int) -> bool {
    &&& 0 <= start < n
    &&& 0 <= len
    &&& forall|k: int|
        0 <= k < len ==> #[trigger] a[(start + k) % n] == 1
}

pub open spec fn rest_run_len_ending_at(a: Seq<i32>, n: int, i: int) -> int
    decreases i + 1,
{
    if i < 0 || i >= 2 * n {
        0
    } else if a[i % n] != 1 {
        0
    } else if i == 0 {
        1
    } else if a[(i - 1) % n] == 1 {
        rest_run_len_ending_at(a, n, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn max_rest_len_upto(a: Seq<i32>, n: int, hi: int) -> int
    decreases hi + 1,
{
    if hi < 0 {
        0
    } else {
        let e = rest_run_len_ending_at(a, n, hi);
        let prev = max_rest_len_upto(a, n, hi - 1);
        if e > prev {
            e
        } else {
            prev
        }
    }
}

proof fn lemma_max_upto_ge_rest_len(a: Seq<i32>, n: int, hi: int, j: int)
    requires
        0 <= j <= hi,
    ensures
        rest_run_len_ending_at(a, n, j) <= max_rest_len_upto(a, n, hi),
    decreases hi - j,
{
    if j == hi {
        assert(max_rest_len_upto(a, n, hi) >= rest_run_len_ending_at(a, n, hi));
    } else {
        lemma_max_upto_ge_rest_len(a, n, hi - 1, j);
        assert(max_rest_len_upto(a, n, hi) >= max_rest_len_upto(a, n, hi - 1));
    }
}

proof fn lemma_max_rest_len_upto_nonneg(a: Seq<i32>, n: int, hi: int)
    requires
        hi >= -1,
    ensures
        max_rest_len_upto(a, n, hi) >= 0,
    decreases hi + 1,
{
    if hi < 0 {
        assert(max_rest_len_upto(a, n, hi) == 0);
    } else {
        lemma_max_rest_len_upto_nonneg(a, n, hi - 1);
        assert(max_rest_len_upto(a, n, hi) >= 0);
    }
}

proof fn lemma_start_plus_k0_mod_n(
    start: int,
    z: int,
    n: int,
) requires
    1 <= n,
    0 <= start < n,
    0 <= z < n,
ensures
    ({
        let k0 = (z - start + n) % n;
        &&& 0 <= k0 < n
        &&& (start + k0) % n == z
    }),
{
    let k0 = (z - start + n) % n;
    if z >= start {
        let diff = z - start;
        assert(0 <= diff < n);
        assert(z - start + n == diff + n);
        assert(k0 == (diff + n) % n);
        lemma_mod_add_multiples_vanish(diff, n);
        assert((diff + n) % n == diff % n);
        lemma_small_mod(diff as nat, n as nat);
        assert(diff % n == diff);
        assert(k0 == diff);
        assert(start + k0 == z);
        lemma_small_mod(z as nat, n as nat);
        assert((start + k0) % n == z);
    } else {
        assert(z < start);
        let t = z - start + n;
        assert(1 <= t);
        assert(t < n);
        assert(k0 == t % n);
        lemma_small_mod(t as nat, n as nat);
        assert(k0 == t);
        assert(start + k0 == z + n);
        assert((start + k0) % n == (z + n) % n);
        lemma_mod_add_multiples_vanish(z, n);
        assert((z + n) % n == z % n);
        lemma_small_mod(z as nat, n as nat);
        assert((start + k0) % n == z);
    }
}

proof fn lemma_circ_len_le_nm1(
    a: Seq<i32>,
    n: int,
    start: int,
    len: int,
) requires
    1 <= n,
    a.len() == n,
    circ_rest_segment(a, n, start, len),
    exists|z: int| 0 <= z < n && #[trigger] a[z] == 0,
ensures
    len <= n - 1,
{
    if len >= n {
        assert(forall|k: int| 0 <= k < len ==> #[trigger] a[(start + k) % n] == 1);
        assert(forall|k: int| 0 <= k < n ==> #[trigger] a[(start + k) % n] == 1);
        assert forall|z: int| 0 <= z < n implies a[z] == 1 by {
            lemma_start_plus_k0_mod_n(start, z, n);
            let k0 = (z - start + n) % n;
            assert(0 <= k0 < n);
            assert(k0 < len);
            assert(a[(start + k0) % n] == 1);
            assert((start + k0) % n == z);
            assert(a[z] == 1);
        };
        assert forall|z: int| 0 <= z < n && a[z] == 0 implies false by {
            assert(a[z] == 1);
            assert(a[z] == 0);
        };
        assert(false);
    }
}

proof fn lemma_rest_run_ge_1_when_a_i_1(
    a: Seq<i32>,
    n: int,
    i: int,
) requires
    1 <= n,
    a.len() == n,
    0 <= i < 2 * n,
    a[i % n] == 1,
ensures
    rest_run_len_ending_at(a, n, i) >= 1,
    decreases i + 1,
{
    reveal_with_fuel(rest_run_len_ending_at, 10);
    if i == 0 {
        assert(rest_run_len_ending_at(a, n, i) == 1);
    } else if a[(i - 1) % n] == 1 {
        lemma_rest_run_ge_1_when_a_i_1(a, n, i - 1);
        assert(rest_run_len_ending_at(a, n, i) == rest_run_len_ending_at(a, n, i - 1) + 1);
    } else {
        assert(rest_run_len_ending_at(a, n, i) == 1);
    }
}

proof fn lemma_prefix_ones_implies_rest_len(
    a: Seq<i32>,
    n: int,
    start: int,
    len: int,
) -> (r: int)
    requires
        1 <= n,
        a.len() == n,
        0 <= start < 2 * n,
        1 <= len,
        start + len <= 2 * n,
        forall|k: int| 0 <= k < len ==> #[trigger] a[(start + k) % n] == 1,
    ensures
        r == rest_run_len_ending_at(a, n, start + len - 1),
        len <= r,
    decreases len,
{
    if len == 1 {
        assert(a[(start + 0) % n] == 1);
        assert(a[start % n] == 1);
        lemma_rest_run_ge_1_when_a_i_1(a, n, start);
        rest_run_len_ending_at(a, n, start)
    } else {
        let last = start + len - 1;
        assert(0 <= last);
        assert(last < 2 * n);
        assert(forall|k: int| 0 <= k < len ==> #[trigger] a[(start + k) % n] == 1);
        assert(a[(start + (len - 1)) % n] == 1);
        assert(forall|k: int| 0 <= k < len - 1 ==> #[trigger] a[(start + k) % n] == 1);
        let r0 = lemma_prefix_ones_implies_rest_len(a, n, start, len - 1);
        assert(r0 == rest_run_len_ending_at(a, n, start + len - 2));
        assert(len - 1 <= r0);
        reveal_with_fuel(rest_run_len_ending_at, 8);
        assert(a[(last - 1) % n] == 1);
        assert(rest_run_len_ending_at(a, n, last) == rest_run_len_ending_at(a, n, last - 1) + 1);
        assert(rest_run_len_ending_at(a, n, last) >= len);
        rest_run_len_ending_at(a, n, last)
    }
}

proof fn lemma_circ_implies_len_le_max(
    a: Seq<i32>,
    n: int,
    start: int,
    len: int,
) requires
    1 <= n,
    a.len() == n,
    circ_rest_segment(a, n, start, len),
    exists|z: int| 0 <= z < n && #[trigger] a[z] == 0,
ensures
    len <= max_rest_len_upto(a, n, 2 * n - 1),
{
    if len == 0 {
        lemma_max_rest_len_upto_nonneg(a, n, 2 * n - 1);
    } else {
        lemma_circ_len_le_nm1(a, n, start, len);
        assert(start + len - 1 < 2 * n);
        let r = lemma_prefix_ones_implies_rest_len(a, n, start, len);
        assert(r == rest_run_len_ending_at(a, n, start + len - 1));
        assert(len <= r);
        lemma_max_upto_ge_rest_len(a, n, 2 * n - 1, start + len - 1);
        assert(r <= max_rest_len_upto(a, n, 2 * n - 1));
    }
}

proof fn lemma_rest_run_means_ones(
    a: Seq<i32>,
    n: int,
    i: int,
    k: int,
)
    requires
        1 <= n,
        a.len() == n,
        0 <= i < 2 * n,
        0 <= k < rest_run_len_ending_at(a, n, i),
    ensures
        a[(i - k) % n] == 1,
    decreases k,
{
    reveal_with_fuel(rest_run_len_ending_at, 10);
    if k == 0 {
        assert(a[i % n] == 1);
        assert(a[(i - 0) % n] == 1);
    } else {
        assert(a[i % n] == 1);
        assert(i > 0);
        assert(a[(i - 1) % n] == 1);
        assert(rest_run_len_ending_at(a, n, i)
            == rest_run_len_ending_at(a, n, i - 1) + 1);
        lemma_rest_run_means_ones(a, n, i - 1, k - 1);
        assert(a[((i - 1) - (k - 1)) % n] == 1);
        assert((i - 1) - (k - 1) == i - k);
    }
}

proof fn lemma_rest_run_bounded_by_n_minus_1(
    a: Seq<i32>,
    n: int,
    i: int,
)
    requires
        1 <= n,
        a.len() == n,
        0 <= i < 2 * n,
        forall|j: int| 0 <= j < n ==> #[trigger] a[j] == 0 || a[j] == 1,
        exists|z: int| 0 <= z < n && #[trigger] a[z] == 0,
    ensures
        rest_run_len_ending_at(a, n, i) <= n - 1,
{
    let r = rest_run_len_ending_at(a, n, i);
    if r >= n {
        assert forall|z: int| 0 <= z < n implies a[z] == 1 by {
            let diff = i - z;
            if diff >= 0 && diff < n {
                let k = diff;
                assert(0 <= k && k < n && k < r);
                lemma_rest_run_means_ones(a, n, i, k);
                assert(a[(i - k) % n] == 1);
                assert(i - k == z);
                lemma_small_mod(z as nat, n as nat);
                assert((i - k) % n == z);
            } else if diff >= n {
                let k = diff - n;
                assert(0 <= k && k < n && k < r);
                lemma_rest_run_means_ones(a, n, i, k);
                assert(a[(i - k) % n] == 1);
                assert(i - k == z + n);
                lemma_mod_add_multiples_vanish(z, n);
                assert((z + n) % n == z % n);
                lemma_small_mod(z as nat, n as nat);
                assert((i - k) % n == z);
            } else {
                let k = diff + n;
                assert(0 < k && k < n && k < r);
                lemma_rest_run_means_ones(a, n, i, k);
                assert(a[(i - k) % n] == 1);
                assert(i - k == z - n);
                lemma_mod_add_multiples_vanish(z - n, n);
                assert((z - n + n) % n == (z - n) % n);
                lemma_small_mod(z as nat, n as nat);
                assert(z % n == z);
                assert((z - n) % n == z);
                assert((i - k) % n == z);
            }
            assert(a[z] == 1);
        };
        let z_wit = choose|z: int| 0 <= z < n && a[z] == 0;
        assert(a[z_wit] == 1);
        assert(false);
    }
}

proof fn lemma_max_rest_len_upto_bounded(
    a: Seq<i32>,
    n: int,
    hi: int,
)
    requires
        1 <= n,
        a.len() == n,
        -1 <= hi < 2 * n,
        forall|j: int| 0 <= j < n ==> #[trigger] a[j] == 0 || a[j] == 1,
        exists|z: int| 0 <= z < n && #[trigger] a[z] == 0,
    ensures
        max_rest_len_upto(a, n, hi) <= n - 1,
    decreases hi + 1,
{
    if hi < 0 {
        assert(max_rest_len_upto(a, n, hi) == 0);
    } else {
        lemma_max_rest_len_upto_bounded(a, n, hi - 1);
        lemma_rest_run_bounded_by_n_minus_1(a, n, hi);
        reveal_with_fuel(max_rest_len_upto, 2);
    }
}

impl Solution {
    pub fn maximal_continuous_rest(a: Vec<i32>) -> (res: i32)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] == 0 || a[i] == 1,
            exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == 0,
        ensures
            0 <= (res as int) && (res as int) <= a.len() as int,
            (res as int) == max_rest_len_upto(a@, a.len() as int, 2 * (a.len() as int) - 1),
    {
        let n = a.len();
        let ghost n_int: int = n as int;
        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut i: usize = 0;
        let total: usize = 2 * n;
        proof {
            assert(n_int == a@.len());
            assert(2 * n_int - 1 >= 0);
        }
        while i < total
            invariant
                1 <= n <= 200_000,
                n == a.len(),
                n_int == a@.len(),
                total == 2 * n,
                forall|j: int| 0 <= j < a.len() ==> #[trigger] a@[j] == 0 || a@[j] == 1,
                exists|j: int| 0 <= j < a.len() && #[trigger] a@[j] == 0,
                i <= total,
                0 <= cur as int <= n_int - 1,
                cur as int == rest_run_len_ending_at(a@, n_int, i as int - 1),
                best as int == max_rest_len_upto(a@, n_int, i as int - 1),
                0 <= best as int <= n_int - 1,
            decreases total - i,
        {
            let idx: usize = i % n;
            proof {
                assert(0 <= i as int);
                assert((i as int) < 2 * n_int);
                assert(0 <= idx as int);
                assert((idx as int) < n_int);
                assert(idx == i % n);
                assert(a@[idx as int] == a@[(i as int) % n_int]);
            }
            if a[idx] == 1 {
                proof {
                    reveal_with_fuel(rest_run_len_ending_at, 10);
                    if i == 0 {
                        assert(cur as int == 0);
                        assert(rest_run_len_ending_at(a@, n_int, -1) == 0);
                        assert(rest_run_len_ending_at(a@, n_int, 0) == 1);
                    } else {
                        assert(cur as int == rest_run_len_ending_at(a@, n_int, (i as int) - 1));
                        if a@[((i as int) - 1) % n_int] == 1 {
                            assert(rest_run_len_ending_at(a@, n_int, i as int)
                                == rest_run_len_ending_at(a@, n_int, (i as int) - 1) + 1);
                        } else {
                            assert(rest_run_len_ending_at(a@, n_int, i as int) == 1);
                            assert(rest_run_len_ending_at(a@, n_int, (i as int) - 1) == 0);
                        }
                    }
                }
                cur = cur + 1;
                proof {
                    reveal_with_fuel(rest_run_len_ending_at, 10);
                    assert(cur as int == rest_run_len_ending_at(a@, n_int, i as int));
                    lemma_rest_run_bounded_by_n_minus_1(a@, n_int, i as int);
                    assert((cur as int) <= n_int - 1);
                }
            } else {
                proof {
                    reveal_with_fuel(rest_run_len_ending_at, 10);
                    assert(rest_run_len_ending_at(a@, n_int, i as int) == 0);
                }
                cur = 0;
                proof {
                    assert(cur as int == rest_run_len_ending_at(a@, n_int, i as int));
                    assert((cur as int) <= n_int - 1);
                }
            }
            let ghost prev_best = best;
            if cur > best {
                best = cur;
            } else {
            }
            proof {
                reveal_with_fuel(max_rest_len_upto, 10);
                assert(cur as int == rest_run_len_ending_at(a@, n_int, i as int));
                assert(max_rest_len_upto(a@, n_int, i as int)
                    == if rest_run_len_ending_at(a@, n_int, i as int)
                        > max_rest_len_upto(a@, n_int, i as int - 1)
                    {
                        rest_run_len_ending_at(a@, n_int, i as int)
                    } else {
                        max_rest_len_upto(a@, n_int, i as int - 1)
                    });
                if cur as int > prev_best as int {
                    assert(best as int == cur as int);
                } else {
                    assert(best as int == prev_best as int);
                }
            }
            assert(best as int == max_rest_len_upto(a@, n_int, i as int));
            i = i + 1;
            proof {
                assert(cur as int == rest_run_len_ending_at(a@, n_int, (i as int) - 1));
            }
        }
        proof {
            assert(i == total);
            assert((i as int) == 2 * n_int);
            assert(best as int == max_rest_len_upto(a@, n_int, 2 * n_int - 1));
            lemma_max_rest_len_upto_bounded(a@, n_int, 2 * n_int - 1);
            assert(best as int <= n_int - 1);
            assert forall|start: int, len: int|
                circ_rest_segment(a@, n_int, start, len) implies len <= best as int by {
                assert forall|start: int, len: int|
                    circ_rest_segment(a@, n_int, start, len) implies len <= best as int by {
                    if circ_rest_segment(a@, n_int, start, len) {
                        lemma_circ_implies_len_le_max(
                            a@,
                            n_int,
                            start,
                            len,
                        );
                    }
                };
            };
        }
        best
    }
}

}