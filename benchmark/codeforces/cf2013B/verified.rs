use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum_upto(s: Seq<i64>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_sum_upto(s, n - 1) + s[n - 1]
    }
}

pub open spec fn spec_battle_answer(s: Seq<i64>) -> int
    recommends
        2 <= s.len(),
{
    let n = s.len() as int;
    spec_sum_upto(s, n) - 2 * s[n - 2]
}

proof fn lemma_spec_sum_upto_succ(s: Seq<i64>, k: int)
    requires
        0 <= k < s.len(),
    ensures
        spec_sum_upto(s, k + 1) == spec_sum_upto(s, k) + s[k],
{
    assert(k + 1 > 0);
    assert(spec_sum_upto(s, k + 1) == spec_sum_upto(s, k) + s[k]);
}

proof fn lemma_prefix_sum_bound(s: Seq<i64>, k: int)
    requires
        0 <= k <= s.len(),
        forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] <= 1_000_000_000,
    ensures
        spec_sum_upto(s, k) <= k * 1_000_000_000,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_prefix_sum_bound(s, (k - 1));
        assert(spec_sum_upto(s, k) == spec_sum_upto(s, k - 1) + s[k - 1]);
        assert(s[k - 1] <= 1_000_000_000);
        assert(spec_sum_upto(s, k - 1) <= (k - 1) * 1_000_000_000);
    }
}

proof fn lemma_sum_at_least_len(s: Seq<i64>, k: int)
    requires
        0 <= k <= s.len(),
        forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] >= 1,
    ensures
        spec_sum_upto(s, k) >= k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_sum_at_least_len(s, k - 1);
        assert(spec_sum_upto(s, k) == spec_sum_upto(s, k - 1) + s[k - 1]);
        assert(s[k - 1] >= 1);
    }
}

impl Solution {
    pub fn battle_for_survive(a: Vec<i64>) -> (res: i64)
        requires
            2 <= a.len() <= 200_000,
            forall|i: int|
                0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
        ensures
            res as int == spec_battle_answer(a@),
    {
        let n = a.len();
        let mut s = 0i64;
        let mut i = 0usize;
        while i < n
            invariant
                n == a.len(),
                2 <= n <= 200_000,
                i <= n,
                s as int == spec_sum_upto(a@, i as int),
                (s as int) <= (i as int) * 1_000_000_000,
                forall|j: int|
                    0 <= j < a.len() ==> 1 <= #[trigger] a[j] && a[j] <= 1_000_000_000,
            decreases n - i,
        {
            proof {
                lemma_spec_sum_upto_succ(a@, i as int);
                lemma_prefix_sum_bound(a@, i as int);
                assert((i as int) < (n as int));
                assert(spec_sum_upto(a@, (i as int) + 1) <= ((i as int) + 1) * 1_000_000_000);
                assert(((i as int) + 1) * 1_000_000_000 <= 200_000 * 1_000_000_000);
                assert(200_000i64 * 1_000_000_000i64 < 9223372036854775807i64);
            }
            s = s + a[i];
            proof {
                assert(s as int == spec_sum_upto(a@, (i as int) + 1));
                lemma_prefix_sum_bound(a@, (i as int) + 1);
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(s as int == spec_sum_upto(a@, n as int));
            assert(spec_battle_answer(a@) == spec_sum_upto(a@, n as int) - 2 * (a@[(n as int) - 2]));
            lemma_prefix_sum_bound(a@, n as int);
            assert((s as int) <= (n as int) * 1_000_000_000);
            assert((a@[(n as int) - 2] as int) * 2 <= 2_000_000_000);
            lemma_sum_at_least_len(a@, n as int);
            assert(spec_sum_upto(a@, n as int) >= n as int);
            assert((s as int) - 2 * (a@[(n as int) - 2]) >= (n as int) - 2_000_000_000);
            assert((n as int) - 2_000_000_000 > -9223372036854775808);
            assert((s as int) - 2 * (a@[(n as int) - 2]) < 9223372036854775807);
        }
        s - 2 * a[n - 2]
    }
}

}
