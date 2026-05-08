use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_sum_prefix(a: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= a.len(),
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        spec_sum_prefix(a, k - 1) + a[k - 1] as int
    }
}

pub open spec fn spec_min_odd_prefix(a: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= a.len(),
    decreases k,
{
    if k <= 0 {
        101
    } else {
        let m = spec_min_odd_prefix(a, k - 1);
        let x = a[k - 1] as int;
        if x % 2 == 1 {
            if m < x {
                m
            } else {
                x
            }
        } else {
            m
        }
    }
}

pub open spec fn max_loving_petals_spec(a: Seq<i32>) -> int {
    let t = spec_sum_prefix(a, a.len() as int);
    let mo = spec_min_odd_prefix(a, a.len() as int);
    if t % 2 == 1 {
        t
    } else {
        if mo == 101 {
            0int
        } else {
            t - mo
        }
    }
}

proof fn lemma_spec_sum_prefix_succ(a: Seq<i32>, k: int)
    requires
        0 <= k < a.len(),
    ensures
        spec_sum_prefix(a, k + 1) == spec_sum_prefix(a, k) + a[k] as int,
{
}

proof fn lemma_final_matches_spec(a: Seq<i32>, total: i32, min_odd: i32)
    requires
        a.len() >= 1,
        total as int == spec_sum_prefix(a, a.len() as int),
        min_odd as int == spec_min_odd_prefix(a, a.len() as int),
        forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 100,
    ensures
        (if total % 2 == 1 {
            total as int
        } else {
            if min_odd == 101 {
                0int
            } else {
                (total - min_odd) as int
            }
        }) == max_loving_petals_spec(a),
{
    let t = spec_sum_prefix(a, a.len() as int);
    let mo = spec_min_odd_prefix(a, a.len() as int);
    assert(total as int == t);
    assert(min_odd as int == mo);
    assert((total as int) % 2 == (t % 2));
    if t % 2 == 1 {
        assert(max_loving_petals_spec(a) == t);
        assert(total % 2 == 1);
    } else {
        assert(max_loving_petals_spec(a) == if mo == 101 { 0int } else { t - mo });
        assert(total % 2 == 0);
        if mo == 101 {
            assert(min_odd == 101);
        } else {
            assert(min_odd != 101);
            assert((total - min_odd) as int == t - mo);
        }
    }
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn max_loving_petals(a: Vec<i32>) -> (result: i32)
        requires
            1 <= a.len() <= 100,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 100,
        ensures
            result as int == max_loving_petals_spec(a@),
    {
        let n = a.len();
        let mut total = 0i32;
        let mut min_odd = 101i32;
        let mut i = 0usize;
        while i < n
            invariant
                n == a.len(),
                1 <= n && n <= 100,
                0 <= i <= n,
                total as int == spec_sum_prefix(a@, i as int),
                min_odd as int == spec_min_odd_prefix(a@, i as int),
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 100,
                0 <= total,
                total as int <= i as int * 100,
                min_odd == 101 || (1 <= min_odd && min_odd <= 100),
        {
            proof {
                lemma_spec_sum_prefix_succ(a@, i as int);
                reveal_with_fuel(spec_min_odd_prefix, 20);
            }
            total = total + a[i];
            if a[i] % 2 == 1 {
                if a[i] < min_odd {
                    min_odd = a[i];
                }
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
        }
        let r = if total % 2 == 1 {
            total
        } else {
            if min_odd == 101 {
                0
            } else {
                total - min_odd
            }
        };
        proof {
            lemma_final_matches_spec(a@, total, min_odd);
            assert(r as int == max_loving_petals_spec(a@));
        }
        r
    }
}

}
