use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map(|_idx: int, x: i32| x as int)
}























pub open spec fn count_above(s: Seq<int>, t: int) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else {
        count_above(s.drop_last(), t)
            + if s.last() > t { s.last() - t } else { 0 }
    }
}

pub open spec fn value_above(s: Seq<int>, t: int) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else {
        value_above(s.drop_last(), t)
            + if s.last() > t { (s.last() + t + 1) * (s.last() - t) / 2 } else { 0 }
    }
}

proof fn lemma_count_above_nonneg(s: Seq<int>, t: int)
    ensures count_above(s, t) >= 0
    decreases s.len()
{
    if s.len() > 0 { lemma_count_above_nonneg(s.drop_last(), t); }
}

proof fn lemma_count_above_monotone(s: Seq<int>, t1: int, t2: int)
    requires t1 <= t2
    ensures count_above(s, t1) >= count_above(s, t2)
    decreases s.len()
{
    if s.len() > 0 { lemma_count_above_monotone(s.drop_last(), t1, t2); }
}

proof fn lemma_count_above_at_max(s: Seq<int>, m: int)
    requires forall |i: int| 0 <= i < s.len() ==> s[i] <= m
    ensures count_above(s, m) == 0
    decreases s.len()
{
    if s.len() > 0 {
        assert forall |i: int| 0 <= i < s.drop_last().len() implies s.drop_last()[i] <= m by {
            assert(s.drop_last()[i] == s[i]);
        }
        lemma_count_above_at_max(s.drop_last(), m);
    }
}

proof fn lemma_count_above_prefix_le(s: Seq<int>, k: int, t: int)
    requires 0 <= k <= s.len()
    ensures count_above(s.take(k), t) <= count_above(s, t)
    decreases s.len()
{
    lemma_count_above_nonneg(s.take(k), t);
    if s.len() > 0 && k < s.len() {
        lemma_count_above_prefix_le(s.drop_last(), k, t);
        assert(s.drop_last().take(k) =~= s.take(k));
    } else if s.len() > 0 {
        assert(s.take(k) =~= s);
    }
}

proof fn lemma_take_drop_last(s: Seq<int>, k: int)
    requires 0 < k <= s.len()
    ensures
        s.take(k).drop_last() =~= s.take(k - 1),
        s.take(k).last() == s[k - 1],
        s.take(k).len() == k,
{
    assert(s.take(k).drop_last() =~= s.take(k - 1));
}

proof fn lemma_value_above_nonneg(s: Seq<int>, t: int)
    requires t >= 0
    ensures value_above(s, t) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        lemma_value_above_nonneg(s.drop_last(), t);
        if s.last() > t {
            assert((s.last() + t + 1) * (s.last() - t) >= 0) by(nonlinear_arith)
                requires s.last() > t, t >= 0;
            assert((s.last() + t + 1) * (s.last() - t) / 2 >= 0) by(nonlinear_arith)
                requires (s.last() + t + 1) * (s.last() - t) >= 0;
        }
    }
}

impl Solution {
    fn count_above_exec(inventory: &Vec<i32>, threshold: i64) -> (count: i64)
        requires
            inventory.len() <= 100_000,
            forall |i: int| 0 <= i < inventory.len() ==> 1 <= #[trigger] inventory[i] <= 1_000_000_000,
            0 <= threshold <= 1_000_000_000,
        ensures
            count as int == count_above(to_int_seq(inventory@), threshold as int),
            count >= 0,
    {
        let ghost sinv = to_int_seq(inventory@);
        let n = inventory.len();
        let mut count: i64 = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == inventory.len(),
                n <= 100_000,
                sinv == to_int_seq(inventory@),
                count as int == count_above(sinv.take(j as int), threshold as int),
                count >= 0,
                forall |i: int| 0 <= i < n ==> 1 <= #[trigger] inventory[i] <= 1_000_000_000,
                0 <= threshold <= 1_000_000_000,
                count <= (j as int) * 1_000_000_000,
            decreases n - j,
        {
            proof {
                lemma_take_drop_last(sinv, (j + 1) as int);
                assert(sinv[j as int] == inventory[j as int] as int);
            }
            if inventory[j] as i64 > threshold {
                count += inventory[j] as i64 - threshold;
            }
            proof {
                assert(count as int == count_above(sinv.take((j + 1) as int), threshold as int));
                assert(count <= ((j + 1) as int) * 1_000_000_000) by(nonlinear_arith)
                    requires
                        count as int <= (j as int) * 1_000_000_000 + 1_000_000_000,
                        0 <= j,
                        j < n,
                        n <= 100_000;
            }
            j += 1;
        }
        proof { assert(sinv.take(n as int) =~= sinv); }
        count
    }

    pub fn max_profit(inventory: Vec<i32>, orders: i32) -> (result: i32)
        requires
            1 <= inventory.len() <= 100_000,
            forall |i: int| 0 <= i < inventory.len() ==> 1 <= #[trigger] inventory[i] <= 1_000_000_000,
            1 <= orders <= 1_000_000_000,
            orders as int <= count_above(to_int_seq(inventory@), 0),
        ensures
            exists |t: int| {
                &&& 0 <= t
                &&& count_above(to_int_seq(inventory@), t) <= orders as int
                &&& (t == 0 || count_above(to_int_seq(inventory@), t - 1) > orders as int)
                &&& result as int == (value_above(to_int_seq(inventory@), t)
                    + (orders as int - count_above(to_int_seq(inventory@), t)) * t)
                    % 1_000_000_007
            },
    {
        let ghost sinv = to_int_seq(inventory@);
        let n = inventory.len();
        let orders_i64 = orders as i64;
        let modulo: i128 = 1_000_000_007;

        let mut max_inv: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == inventory.len(),
                0 <= max_inv <= 1_000_000_000,
                forall |j: int| 0 <= j < i ==> inventory[j] as i64 <= max_inv,
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] inventory[j] <= 1_000_000_000,
            decreases n - i,
        {
            if inventory[i] as i64 > max_inv {
                max_inv = inventory[i] as i64;
            }
            i += 1;
        }

        proof {
            assert forall |j: int| 0 <= j < sinv.len() implies sinv[j] <= max_inv as int by {
                assert(sinv[j] == inventory[j] as int);
                assert(inventory[j] as i64 <= max_inv);
            };
            lemma_count_above_at_max(sinv, max_inv as int);
        }

        let mut lo: i64 = 0;
        let mut hi: i64 = max_inv;
        while lo < hi
            invariant
                0 <= lo <= hi <= max_inv,
                max_inv <= 1_000_000_000,
                count_above(sinv, hi as int) <= orders_i64 as int,
                lo == 0 || count_above(sinv, lo as int - 1) > orders_i64 as int,
                sinv == to_int_seq(inventory@),
                n == inventory.len(),
                inventory.len() <= 100_000,
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] inventory[j] <= 1_000_000_000,
                orders_i64 == orders as i64,
                1 <= orders_i64 <= 1_000_000_000,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            let count = Self::count_above_exec(&inventory, mid);
            if count <= orders_i64 {
                hi = mid;
            } else {
                proof {
                    if mid + 1 > 1 {
                        lemma_count_above_monotone(sinv, mid as int, mid as int);
                    }
                }
                lo = mid + 1;
            }
        }

        let threshold = lo;

        let mut total: i128 = 0;
        let mut sold: i64 = 0;
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == inventory.len(),
                n <= 100_000,
                sinv == to_int_seq(inventory@),
                total as int == value_above(sinv.take(k as int), threshold as int),
                sold as int == count_above(sinv.take(k as int), threshold as int),
                0 <= threshold <= max_inv,
                max_inv <= 1_000_000_000,
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] inventory[j] <= 1_000_000_000,
                sold >= 0,
                sold <= orders_i64,
                total >= 0,
                (total as int) <= (k as int) * 2_000_000_001_000_000_000int,
                orders_i64 == orders as i64,
                1 <= orders_i64 <= 1_000_000_000,
                count_above(sinv, threshold as int) <= orders_i64 as int,
                forall |j: int| 0 <= j < sinv.len() ==> sinv[j] <= max_inv as int,
            decreases n - k,
        {
            let inv = inventory[k] as i64;

            proof {
                lemma_take_drop_last(sinv, (k + 1) as int);
                assert(sinv[k as int] == inventory[k as int] as int);
            }

            if inv > threshold {
                proof {
                    lemma_count_above_prefix_le(sinv, (k + 1) as int, threshold as int);
                }

                sold += inv - threshold;

                let inv128 = inv as i128;
                let thr128 = threshold as i128;

                assert(1 <= inv128 && inv128 <= 1_000_000_000);
                assert(0 <= thr128 && thr128 <= 1_000_000_000);
                assert(inv128 > thr128);

                let a = inv128 + thr128 + 1;
                let b = inv128 - thr128;

                assert(2 <= a && a <= 2_000_000_001);
                assert(1 <= b && b <= 1_000_000_000);

                assert(a * b <= 2_000_000_001_000_000_000i128) by(nonlinear_arith)
                    requires a <= 2_000_000_001, b <= 1_000_000_000, a >= 0, b >= 0;

                let contrib = (inv128 + thr128 + 1) * (inv128 - thr128) / 2;

                proof {
                    assert(contrib == a * b / 2);
                    assert(a * b >= 0);
                    assert(contrib >= 0);
                    assert(contrib <= a * b);
                    assert(contrib <= 2_000_000_001_000_000_000i128);
                    assert((total as int) + (contrib as int) <= ((k + 1) as int) * 2_000_000_001_000_000_000int)
                        by(nonlinear_arith)
                        requires
                            (total as int) <= (k as int) * 2_000_000_001_000_000_000int,
                            (contrib as int) <= 2_000_000_001_000_000_000int,
                            total >= 0i128,
                            contrib >= 0i128;
                }

                total += contrib;
            }

            proof {
                assert(total as int == value_above(sinv.take((k + 1) as int), threshold as int));
                assert(sold as int == count_above(sinv.take((k + 1) as int), threshold as int));
                assert(sold <= orders_i64) by {
                    lemma_count_above_prefix_le(sinv, (k + 1) as int, threshold as int);
                }
                lemma_value_above_nonneg(sinv.take((k + 1) as int), threshold as int);
            }

            k += 1;
        }

        proof { assert(sinv.take(n as int) =~= sinv); }

        assert(sold <= orders_i64) by {
            assert(sold as int == count_above(sinv, threshold as int));
            assert(count_above(sinv, threshold as int) <= orders_i64 as int);
        }

        let rem128 = (orders_i64 - sold) as i128;
        let thr_rem = threshold as i128;

        assert(0 <= rem128 && rem128 <= 1_000_000_000);
        assert(0 <= thr_rem && thr_rem <= 1_000_000_000);
        assert(rem128 * thr_rem <= 1_000_000_000_000_000_000i128) by(nonlinear_arith)
            requires rem128 >= 0, rem128 <= 1_000_000_000, thr_rem >= 0, thr_rem <= 1_000_000_000;

        total += rem128 * thr_rem;

        proof {
            assert(total as int == value_above(sinv, threshold as int)
                + (orders as int - count_above(sinv, threshold as int)) * threshold as int);
            lemma_value_above_nonneg(sinv, threshold as int);
            assert(total >= 0);
        }

        (total % modulo) as i32
    }
}

}
