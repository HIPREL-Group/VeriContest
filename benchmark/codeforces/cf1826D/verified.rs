use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_neg_inf() -> int {
    -1_000_000_000_000_000
}

pub open spec fn spec_max2(a: int, b: int) -> int {
    if a >= b {
        a
    } else {
        b
    }
}

pub open spec fn spec_dp_state(b: Seq<i32>, k: nat) -> (int, int, int)
    recommends
        k <= b.len(),
    decreases k,
{
    if k == 0 {
        (spec_neg_inf(), spec_neg_inf(), spec_neg_inf())
    } else {
        let (res0, dp10, dp20) = spec_dp_state(b, (k - 1) as nat);
        let bi = b[(k - 1) as int] as int;
        let ii = (k - 1) as int;
        let cand = dp20 + bi - ii;
        let new_res = spec_max2(res0, cand);
        let new_dp2 = spec_max2(dp20, dp10 + bi);
        let new_dp1 = spec_max2(dp10, bi + ii);
        (new_res, new_dp1, new_dp2)
    }
}

pub open spec fn spec_best_score(b: Seq<i32>) -> int {
    spec_dp_state(b, b.len() as nat).0
}

proof fn lemma_spec_dp_step(b: Seq<i32>, k: nat)
    requires
        k < b.len(),
    ensures
        spec_dp_state(b, (k + 1) as nat)
            == ({
                let (res0, dp10, dp20) = spec_dp_state(b, k);
                let bi = b[k as int] as int;
                let ii = k as int;
                let cand = dp20 + bi - ii;
                let new_res = spec_max2(res0, cand);
                let new_dp2 = spec_max2(dp20, dp10 + bi);
                let new_dp1 = spec_max2(dp10, bi + ii);
                (new_res, new_dp1, new_dp2)
            }),
{
    reveal_with_fuel(spec_dp_state, 4);
}


proof fn lemma_spec_dp_prefix_upper(b: Seq<i32>, k: nat)
    requires
        k <= b.len(),
        b.len() <= 100_000,
        forall|j: int|
            #![trigger b[j]]
            0 <= j && j < b.len() ==> 1 <= b[j] as int && b[j] as int <= 100_000_000,
    ensures
        ({
            let (r, d1, d2) = spec_dp_state(b, k);
            let c: int = 200_000_000;
            r <= k as int * c && d1 <= k as int * c && d2 <= k as int * c
        }),
    decreases k,
{
    reveal_with_fuel(spec_dp_state, 2);
    let c: int = 200_000_000;
    if k == 0 {
        assert(spec_neg_inf() <= 0);
        assert(spec_neg_inf() <= k as int * c);
    } else {
        lemma_spec_dp_prefix_upper(b, (k - 1) as nat);
        let (res0, dp10, dp20) = spec_dp_state(b, (k - 1) as nat);
        let bi = b[(k - 1) as int] as int;
        let ii = (k - 1) as int;
        assert(res0 <= (k - 1) as int * c);
        assert(dp10 <= (k - 1) as int * c);
        assert(dp20 <= (k - 1) as int * c);
        assert(1 <= bi && bi <= 100_000_000);
        assert(0 <= ii && ii < 100_000);
        assert((k - 1) as int * c + 100_000_000 <= k as int * c);
        let cand = dp20 + bi - ii;
        let new_res = spec_max2(res0, cand);
        let new_dp2 = spec_max2(dp20, dp10 + bi);
        let new_dp1 = spec_max2(dp10, bi + ii);
        assert(cand <= (k - 1) as int * c + bi);
        assert(cand <= k as int * c);
        assert(new_res <= k as int * c);
        assert(dp10 + bi <= k as int * c);
        assert(new_dp2 <= k as int * c);
        assert(bi + ii <= k as int * c);
        assert(new_dp1 <= k as int * c);
        assert(spec_dp_state(b, k) == (new_res, new_dp1, new_dp2));
    }
}

proof fn lemma_spec_dp_components_ge_neg_inf(b: Seq<i32>, k: nat)
    requires
        k <= b.len(),
        b.len() <= 100_000,
        forall|j: int|
            #![trigger b[j]]
            0 <= j && j < b.len() ==> 1 <= b[j] as int && b[j] as int <= 100_000_000,
    ensures
        ({
            let (r, d1, d2) = spec_dp_state(b, k);
            r >= spec_neg_inf() && d1 >= spec_neg_inf() && d2 >= spec_neg_inf()
        }),
    decreases k,
{
    reveal_with_fuel(spec_dp_state, 2);
    if k == 0 {
    } else {
        lemma_spec_dp_components_ge_neg_inf(b, (k - 1) as nat);
        let (res0, dp10, dp20) = spec_dp_state(b, (k - 1) as nat);
        let bi = b[(k - 1) as int] as int;
        let ii = (k - 1) as int;
        assert(res0 >= spec_neg_inf());
        assert(dp10 >= spec_neg_inf());
        assert(dp20 >= spec_neg_inf());
        assert(1 <= bi && bi <= 100_000_000);
        assert(0 <= ii && ii < b.len() as int);
        let cand = dp20 + bi - ii;
        assert(cand >= spec_neg_inf() + 1 - (b.len() as int - 1));
        assert(spec_max2(res0, cand) >= spec_neg_inf());
        assert(spec_max2(dp20, dp10 + bi) >= spec_neg_inf());
        assert(spec_max2(dp10, bi + ii) >= spec_neg_inf());
    }
}


proof fn lemma_spec_max2_exec_order(a: int, b: int, ax: i64, bx: i64)
    requires
        a == ax as int,
        b == bx as int,
    ensures
        spec_max2(a, b) == (if bx > ax {
            bx
        } else {
            ax
        }) as int,
{
    if bx > ax {
        assert(b > a);
    } else {
        assert(b <= a);
    }
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn best_running_miles(b: &Vec<i32>) -> (result: i64)
        requires
            3 <= b.len() <= 100_000,
            forall|j: int|
                #![trigger b[j]]
                0 <= j && j < b.len() ==> 1 <= b[j] as int && b[j] as int <= 100_000_000,
        ensures
            result == spec_best_score(b@),
    {
        let neg_inf: i64 = -1000000000000000i64;
        let mut res = neg_inf;
        let mut dp1 = neg_inf;
        let mut dp2 = neg_inf;
        let mut i = 0usize;
        while i < b.len()
            invariant
                i <= b.len(),
                3 <= b.len() <= 100_000,
                forall|j: int|
                    #![trigger b[j]]
                    0 <= j && j < b.len() ==> 1 <= b[j] as int && b[j] as int <= 100_000_000,
                (res as int) == spec_dp_state(b@, i as nat).0,
                (dp1 as int) == spec_dp_state(b@, i as nat).1,
                (dp2 as int) == spec_dp_state(b@, i as nat).2,
            decreases b.len() - i,
        {
            proof {
                assert(i < b.len());
                lemma_spec_dp_step(b@, i as nat);
                lemma_spec_dp_prefix_upper(b@, i as nat);
                lemma_spec_dp_components_ge_neg_inf(b@, i as nat);
            }
            let bi = b[i] as i64;
            let ii = i as i64;
            let cand128: i128 = (dp2 as i128) + (bi as i128) - (ii as i128);
            let res128: i128 = res as i128;
            let res_old = res;
            if cand128 > res128 {
                res = cand128 as i64;
            }
            let t2: i128 = (dp1 as i128) + (bi as i128);
            let dp2_128: i128 = dp2 as i128;
            let dp2_old = dp2;
            if t2 > dp2_128 {
                dp2 = t2 as i64;
            }
            let t1: i128 = (bi as i128) + (ii as i128);
            let dp1_128: i128 = dp1 as i128;
            let dp1_old = dp1;
            if t1 > dp1_128 {
                dp1 = t1 as i64;
            }
            proof {
                let res0 = spec_dp_state(b@, i as nat).0;
                let dp10 = spec_dp_state(b@, i as nat).1;
                let dp20 = spec_dp_state(b@, i as nat).2;
                let cand_spec = dp20 + (b[i as int] as int) - (i as int);
                assert((res_old as int) == res0);
                assert((dp1_old as int) == dp10);
                assert((dp2_old as int) == dp20);
                assert(cand128 as int == cand_spec);
                assert(res128 as int == res0);
                assert(t2 as int == dp10 + (bi as int));
                assert(dp2_128 as int == dp20);
                assert(t1 as int == (bi as int) + (ii as int));
                assert(dp1_128 as int == dp10);
                assert(dp20 <= i as int * 200_000_000);
                assert(dp10 <= i as int * 200_000_000);
                assert(res0 <= i as int * 200_000_000);
                assert(1 <= (bi as int) && (bi as int) <= 100_000_000);
                assert(0 <= (i as int) && (i as int) < 100_000);
                assert(cand_spec <= i as int * 200_000_000 + 100_000_000);
                assert(cand_spec >= spec_neg_inf() - 100_000);
                assert(cand_spec < 9223372036854775807);
                assert(cand_spec > -9223372036854775808);
                assert((cand128 as i64) as int == cand_spec);
                lemma_spec_max2_exec_order(res0, cand_spec, res_old, (cand128 as i64));
                assert((res as int) == spec_max2(res0, cand_spec));
                assert((dp10 + (bi as int)) < 9223372036854775807);
                assert((dp10 + (bi as int)) > -9223372036854775808);
                assert((t2 as i64) as int == dp10 + (bi as int));
                lemma_spec_max2_exec_order(dp20, dp10 + (bi as int), dp2_old, (t2 as i64));
                assert((dp2 as int) == spec_max2(dp20, dp10 + (bi as int)));
                assert(((bi as int) + (ii as int)) < 9223372036854775807);
                assert(((bi as int) + (ii as int)) > -9223372036854775808);
                assert((t1 as i64) as int == (bi as int) + (ii as int));
                lemma_spec_max2_exec_order(dp10, (bi as int) + (ii as int), dp1_old, (t1 as i64));
                assert((dp1 as int) == spec_max2(dp10, (bi as int) + (ii as int)));
                assert(spec_dp_state(b@, (i + 1) as nat) == (
                    spec_max2(res0, cand_spec),
                    spec_max2(dp10, (bi as int) + (ii as int)),
                    spec_max2(dp20, dp10 + (bi as int)),
                ));
                assert((res as int) == spec_dp_state(b@, (i + 1) as nat).0);
                assert((dp1 as int) == spec_dp_state(b@, (i + 1) as nat).1);
                assert((dp2 as int) == spec_dp_state(b@, (i + 1) as nat).2);
                lemma_spec_dp_prefix_upper(b@, (i + 1) as nat);
                assert((res as int) <= (i + 1) as int * 200_000_000);
                assert((res as int) > -9223372036854775808 && (res as int) < 9223372036854775807);
                assert((dp1 as int) > -9223372036854775808 && (dp1 as int) < 9223372036854775807);
                assert((dp2 as int) > -9223372036854775808 && (dp2 as int) < 9223372036854775807);
            }
            i = i + 1;
        }
        proof {
            assert((res as int) == spec_dp_state(b@, b.len() as nat).0);
        }
        res
    }
}

}
