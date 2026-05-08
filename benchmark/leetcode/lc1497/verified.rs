use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn remainder_count(arr: Seq<i32>, k: int, r: int) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else if arr.last() as int % k == r {
        1 + remainder_count(arr.drop_last(), k, r)
    } else {
        remainder_count(arr.drop_last(), k, r)
    }
}

proof fn remainder_count_nonneg(arr: Seq<i32>, k: int, r: int)
    requires
        k > 0,
    ensures
        remainder_count(arr, k, r) >= 0,
    decreases arr.len(),
{
    if arr.len() > 0 {
        remainder_count_nonneg(arr.drop_last(), k, r);
    }
}

proof fn remainder_count_bound(arr: Seq<i32>, k: int, r: int)
    requires
        k > 0,
    ensures
        remainder_count(arr, k, r) <= arr.len(),
    decreases arr.len(),
{
    if arr.len() > 0 {
        remainder_count_bound(arr.drop_last(), k, r);
    }
}

proof fn lemma_euclid_unique(a: int, k: int, q: int, r: int)
    requires
        k > 0,
        a == k * q + r,
        0 <= r,
        r < k,
    ensures
        r == a % k,
{
    lemma_fundamental_div_mod(a, k);
    assert(r == a % k) by (nonlinear_arith)
        requires
            a == k * q + r,
            a == k * (a / k) + (a % k),
            0 <= r,
            r < k,
            0 <= a % k,
            a % k < k,
            k > 0;
}

impl Solution {
    pub fn can_arrange(arr: Vec<i32>, k: i32) -> (result: bool)
        requires
            arr@.len() % 2 == 0,
            2 <= arr@.len() <= 100000,
            1 <= k <= 100000,
            forall|i: int| 0 <= i < arr@.len() ==> -1000000000 <= #[trigger] arr@[i] <= 1000000000,
        ensures
            result == (remainder_count(arr@, k as int, 0) % 2 == 0 && forall|r: int|
                1 <= r < k as int ==> #[trigger] remainder_count(arr@, k as int, r)
                    == remainder_count(arr@, k as int, k as int - r)),
    {
        let n = arr.len();
        let ku = k as usize;
        let mut count: Vec<i32> = Vec::new();
        let mut init = 0usize;
        while init < ku
            invariant
                0 <= init <= ku,
                ku == k as usize,
                1 <= k <= 100000,
                count@.len() == init as int,
                forall|j: int| 0 <= j < init as int ==> count@[j] == 0i32,
            decreases ku - init,
        {
            count.push(0i32);
            init += 1;
        }
        proof {
            assert forall|r: int| 0 <= r < k as int implies #[trigger] count@[r] as int
                == remainder_count(arr@.take(0int), k as int, r) by {
                assert(arr@.take(0int).len() == 0);
            };
        }
        let mut i = 0usize;
        while i < n
            invariant
                0 <= i <= n,
                n == arr@.len(),
                n <= 100000,
                ku == k as usize,
                1 <= k <= 100000,
                count@.len() == ku as int,
                forall|r: int|
                    0 <= r < k as int ==> #[trigger] count@[r] as int == remainder_count(
                        arr@.take(i as int),
                        k as int,
                        r,
                    ),
                forall|r: int|
                    0 <= r < k as int ==> 0 <= #[trigger] count@[r] as int <= i as int,
                forall|idx: int|
                    0 <= idx < arr@.len() ==> -1000000000 <= #[trigger] arr@[idx] <= 1000000000,
            decreases n - i,
        {
            let elem = arr[i];
            let rem: i32;
            if elem >= 0 {
                rem = elem % k;
            } else {
                let neg_elem = -elem;
                let r = neg_elem % k;
                rem = if r == 0 { 0 } else { k - r };
                proof {
                    let ne = neg_elem as int;
                    let k_int = k as int;
                    let r_int = r as int;
                    lemma_fundamental_div_mod(ne, k_int);
                    assert(r_int == ne % k_int);
                    assert(elem as int == -ne);
                    if r_int == 0 {
                        assert(ne == k_int * (ne / k_int));
                        assert(elem as int == k_int * (-(ne / k_int)) + 0) by (nonlinear_arith)
                            requires ne == k_int * (ne / k_int), elem as int == -ne;
                        lemma_euclid_unique(elem as int, k_int, -(ne / k_int), 0);
                    } else {
                        let q = -(ne / k_int) - 1;
                        assert(elem as int == k_int * q + (k_int - r_int)) by (nonlinear_arith)
                            requires ne == k_int * (ne / k_int) + r_int, elem as int == -ne, q == -(ne / k_int) - 1;
                        lemma_euclid_unique(elem as int, k_int, q, k_int - r_int);
                    }
                }
            }
            let rem_u = rem as usize;
            proof {
                let k_int = k as int;
                assert(rem as int == elem as int % k_int);
                assert(arr@.take((i + 1) as int).drop_last() =~= arr@.take(i as int));
                assert(arr@.take((i + 1) as int).last() == arr@[i as int]);
                remainder_count_nonneg(arr@.take(i as int), k_int, rem as int);
                remainder_count_bound(arr@.take(i as int), k_int, rem as int);
                assert(count@[rem as int] as int <= i as int);
                assert(i < 100000usize);
            }
            count.set(rem_u, count[rem_u] + 1);
            proof {
                let k_int = k as int;
                assert forall|r: int| 0 <= r < k_int implies #[trigger] count@[r] as int
                    == remainder_count(arr@.take((i + 1) as int), k_int, r) by {
                    let seq_next = arr@.take((i + 1) as int);
                    assert(seq_next.drop_last() =~= arr@.take(i as int));
                    assert(seq_next.last() == arr@[i as int]);
                    if r == rem as int {
                        assert(seq_next.last() as int % k_int == r);
                    } else {
                        assert(seq_next.last() as int % k_int != r);
                    }
                };
            }
            i += 1;
        }
        proof {
            assert(arr@.take(n as int) =~= arr@);
        }
        if count[0] % 2 != 0 {
            return false;
        }
        let mut j = 1usize;
        while j < ku
            invariant
                1 <= j <= ku,
                ku == k as usize,
                1 <= k <= 100000,
                count@.len() == ku as int,
                count@[0int] as int % 2 == 0,
                forall|r: int|
                    1 <= r < j as int ==> #[trigger] count@[r] == count@[k as int - r],
                forall|r: int|
                    0 <= r < k as int ==> #[trigger] count@[r] as int == remainder_count(
                        arr@,
                        k as int,
                        r,
                    ),
            decreases ku - j,
        {
            if count[j] != count[ku - j] {
                proof {
                    assert(count@[j as int] != count@[k as int - j as int]);
                }
                return false;
            }
            j += 1;
        }
        proof {
            assert forall|r: int| 1 <= r < k as int implies #[trigger] remainder_count(
                arr@,
                k as int,
                r,
            ) == remainder_count(arr@, k as int, k as int - r) by {
                assert(count@[r] == count@[k as int - r]);
                assert(count@[r] as int == remainder_count(arr@, k as int, r));
                assert(count@[k as int - r] as int == remainder_count(arr@, k as int, k as int - r));
            };
        }
        true
    }
}

}
