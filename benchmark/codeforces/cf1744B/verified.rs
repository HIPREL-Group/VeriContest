use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn apply_one(sum: int, ce: int, co: int, qtype: u32, x: u32) -> (int, int, int) {
    if qtype == 0u32 {
        let new_sum = sum + ce * (x as int);
        if x % 2 == 0 {
            (new_sum, ce, co)
        } else {
            (new_sum, 0, co + ce)
        }
    } else {
        let new_sum = sum + co * (x as int);
        if x % 2 == 0 {
            (new_sum, ce, co)
        } else {
            (new_sum, ce + co, 0)
        }
    }
}

pub open spec fn state_after(s0: int, ce0: int, co0: int, qtypes: Seq<u32>, qxs: Seq<u32>, k: int) -> (int, int, int)
    recommends 0 <= k <= qtypes.len(), qtypes.len() == qxs.len(),
    decreases k,
{
    if k <= 0 {
        (s0, ce0, co0)
    } else {
        let prev = state_after(s0, ce0, co0, qtypes, qxs, k - 1);
        apply_one(prev.0, prev.1, prev.2, qtypes[k - 1], qxs[k - 1])
    }
}

pub open spec fn initial_sum(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 { 0int } else { a[0] as int + initial_sum(a.subrange(1, a.len() as int)) }
}

pub open spec fn initial_even_count(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 { 0int }
    else {
        let rest = initial_even_count(a.subrange(1, a.len() as int));
        if a[0] % 2 == 0 { rest + 1 } else { rest }
    }
}

pub open spec fn initial_odd_count(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 { 0int }
    else {
        let rest = initial_odd_count(a.subrange(1, a.len() as int));
        if a[0] % 2 == 1 { rest + 1 } else { rest }
    }
}

pub open spec fn sum_prefix(a: Seq<u32>, k: int) -> int
    recommends 0 <= k <= a.len(),
    decreases k,
{
    if k <= 0 { 0int } else { a[k - 1] as int + sum_prefix(a, k - 1) }
}

pub open spec fn even_count_prefix(a: Seq<u32>, k: int) -> int
    recommends 0 <= k <= a.len(),
    decreases k,
{
    if k <= 0 { 0int }
    else {
        let prev = even_count_prefix(a, k - 1);
        if a[k - 1] % 2 == 0 { prev + 1 } else { prev }
    }
}

pub open spec fn odd_count_prefix(a: Seq<u32>, k: int) -> int
    recommends 0 <= k <= a.len(),
    decreases k,
{
    if k <= 0 { 0int }
    else {
        let prev = odd_count_prefix(a, k - 1);
        if a[k - 1] % 2 == 1 { prev + 1 } else { prev }
    }
}

proof fn lemma_sum_prefix_full(a: Seq<u32>)
    ensures sum_prefix(a, a.len() as int) == initial_sum(a),
{
    lemma_sum_prefix_eq(a, a.len() as int);
    assert(a.subrange(0, a.len() as int) =~= a);
}

proof fn lemma_sum_prefix_eq(a: Seq<u32>, k: int)
    requires 0 <= k <= a.len(),
    ensures sum_prefix(a, k) == initial_sum(a.subrange(0, k)),
    decreases k,
{
    if k <= 0 {
        assert(a.subrange(0, 0).len() == 0);
    } else {
        lemma_sum_prefix_eq(a, k - 1);
        lemma_initial_sum_extend(a, k);
    }
}

proof fn lemma_initial_sum_extend(a: Seq<u32>, k: int)
    requires 1 <= k <= a.len(),
    ensures initial_sum(a.subrange(0, k)) == initial_sum(a.subrange(0, k - 1)) + a[k - 1] as int,
    decreases k,
{
    if k == 1 {
        assert(a.subrange(0, 1).len() == 1);
        assert(a.subrange(0, 1)[0] == a[0]);
        assert(a.subrange(0, 1).subrange(1, 1).len() == 0);
        assert(initial_sum(a.subrange(0, 1).subrange(1, 1)) == 0);
        assert(initial_sum(a.subrange(0, 1)) == a[0] as int);
        assert(a.subrange(0, 0).len() == 0);
        assert(initial_sum(a.subrange(0, 0)) == 0);
    } else {
        let a_tail = a.subrange(1, a.len() as int);
        lemma_initial_sum_extend(a_tail, k - 1);
        assert(a_tail.subrange(0, k - 1) =~= a.subrange(1, k));
        assert(a_tail.subrange(0, k - 2) =~= a.subrange(1, k - 1));
        assert(a_tail[k - 2] == a[k - 1]);
        assert(a.subrange(0, k).subrange(1, k) =~= a.subrange(1, k));
        assert(a.subrange(0, k - 1).subrange(1, k - 1) =~= a.subrange(1, k - 1));
    }
}

proof fn lemma_even_count_prefix_full(a: Seq<u32>)
    ensures even_count_prefix(a, a.len() as int) == initial_even_count(a),
{
    lemma_even_count_eq(a, a.len() as int);
    assert(a.subrange(0, a.len() as int) =~= a);
}

proof fn lemma_even_count_eq(a: Seq<u32>, k: int)
    requires 0 <= k <= a.len(),
    ensures even_count_prefix(a, k) == initial_even_count(a.subrange(0, k)),
    decreases k,
{
    if k <= 0 {
        assert(a.subrange(0, 0).len() == 0);
    } else {
        lemma_even_count_eq(a, k - 1);
        lemma_initial_even_count_extend(a, k);
    }
}

proof fn lemma_initial_even_count_extend(a: Seq<u32>, k: int)
    requires 1 <= k <= a.len(),
    ensures initial_even_count(a.subrange(0, k)) == initial_even_count(a.subrange(0, k - 1)) + (if a[k - 1] % 2 == 0 { 1int } else { 0int }),
    decreases k,
{
    if k == 1 {
        let s1 = a.subrange(0, 1);
        let s0 = a.subrange(0, 0);
        assert(s1.len() == 1);
        assert(s1[0] == a[0]);
        assert(s1.subrange(1, 1).len() == 0);
        assert(initial_even_count(s1.subrange(1, 1)) == 0);
        assert(initial_even_count(s1) == (if a[0] % 2 == 0 { 1int } else { 0int }));
        assert(s0.len() == 0);
        assert(initial_even_count(s0) == 0);
    } else {
        let a_tail = a.subrange(1, a.len() as int);
        lemma_initial_even_count_extend(a_tail, k - 1);
        assert(a_tail.subrange(0, k - 1) =~= a.subrange(1, k));
        assert(a_tail.subrange(0, k - 2) =~= a.subrange(1, k - 1));
        assert(a_tail[k - 2] == a[k - 1]);
        let sk = a.subrange(0, k);
        let skm1 = a.subrange(0, k - 1);
        assert(sk[0] == a[0]);
        assert(skm1[0] == a[0]);
        assert(sk.subrange(1, k) =~= a.subrange(1, k));
        assert(skm1.subrange(1, k - 1) =~= a.subrange(1, k - 1));
        
        
        
        
    }
}

proof fn lemma_odd_count_prefix_full(a: Seq<u32>)
    ensures odd_count_prefix(a, a.len() as int) == initial_odd_count(a),
{
    lemma_odd_count_eq(a, a.len() as int);
    assert(a.subrange(0, a.len() as int) =~= a);
}

proof fn lemma_odd_count_eq(a: Seq<u32>, k: int)
    requires 0 <= k <= a.len(),
    ensures odd_count_prefix(a, k) == initial_odd_count(a.subrange(0, k)),
    decreases k,
{
    if k <= 0 {
        assert(a.subrange(0, 0).len() == 0);
    } else {
        lemma_odd_count_eq(a, k - 1);
        lemma_initial_odd_count_extend(a, k);
    }
}

proof fn lemma_initial_odd_count_extend(a: Seq<u32>, k: int)
    requires 1 <= k <= a.len(),
    ensures initial_odd_count(a.subrange(0, k)) == initial_odd_count(a.subrange(0, k - 1)) + (if a[k - 1] % 2 == 1 { 1int } else { 0int }),
    decreases k,
{
    if k == 1 {
        let s1 = a.subrange(0, 1);
        let s0 = a.subrange(0, 0);
        assert(s1.len() == 1);
        assert(s1[0] == a[0]);
        assert(s1.subrange(1, 1).len() == 0);
        assert(initial_odd_count(s1.subrange(1, 1)) == 0);
        assert(s0.len() == 0);
        assert(initial_odd_count(s0) == 0);
    } else {
        let a_tail = a.subrange(1, a.len() as int);
        lemma_initial_odd_count_extend(a_tail, k - 1);
        assert(a_tail.subrange(0, k - 1) =~= a.subrange(1, k));
        assert(a_tail.subrange(0, k - 2) =~= a.subrange(1, k - 1));
        assert(a_tail[k - 2] == a[k - 1]);
        let sk = a.subrange(0, k);
        let skm1 = a.subrange(0, k - 1);
        assert(sk[0] == a[0]);
        assert(skm1[0] == a[0]);
        assert(sk.subrange(1, k) =~= a.subrange(1, k));
        assert(skm1.subrange(1, k - 1) =~= a.subrange(1, k - 1));
    }
}

impl Solution {
    pub fn even_odd_sums(a: Vec<u32>, n: usize, qtypes: Vec<u32>, qxs: Vec<u32>, q: usize) -> (result: Vec<i64>)
        requires
            1 <= n <= 100_000,
            1 <= q <= 100_000,
            a.len() == n,
            qtypes.len() == q,
            qxs.len() == q,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < qtypes.len() ==> #[trigger] qtypes[i] <= 1,
            forall|i: int| 0 <= i < qxs.len() ==> 1 <= #[trigger] qxs[i] <= 10_000,
        ensures
            result.len() == q,
            forall|k: int| 0 <= k < q ==> #[trigger] result[k] as int == state_after(
                initial_sum(a@), initial_even_count(a@), initial_odd_count(a@),
                qtypes@, qxs@, k + 1
            ).0,
    {
        let mut sum: i64 = 0;
        let mut ce: i64 = 0;
        let mut co: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100_000,
                a.len() == n,
                forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
                0 <= i <= n,
                sum as int == sum_prefix(a@, i as int),
                ce as int == even_count_prefix(a@, i as int),
                co as int == odd_count_prefix(a@, i as int),
                sum >= 0,
                ce >= 0,
                co >= 0,
                ce + co == i as i64,
                sum <= (i as i64) * 1_000_000_000,
                ce <= i as i64,
                co <= i as i64,
            decreases n - i,
        {
            sum += a[i] as i64;
            if a[i] % 2 == 0 {
                ce += 1;
            } else {
                co += 1;
            }
            i += 1;
        }
        proof {
            lemma_sum_prefix_full(a@);
            lemma_even_count_prefix_full(a@);
            lemma_odd_count_prefix_full(a@);
        }
        let s0: i64 = sum;
        let ce0: i64 = ce;
        let co0: i64 = co;
        let mut result: Vec<i64> = Vec::with_capacity(q);
        let mut k: usize = 0;
        
        
        while k < q
            invariant
                1 <= n <= 100_000,
                1 <= q <= 100_000,
                qtypes.len() == q,
                qxs.len() == q,
                forall|kk: int| 0 <= kk < qtypes.len() ==> #[trigger] qtypes[kk] <= 1,
                forall|kk: int| 0 <= kk < qxs.len() ==> 1 <= #[trigger] qxs[kk] <= 10_000,
                0 <= k <= q,
                result.len() == k,
                s0 as int == initial_sum(a@),
                ce0 as int == initial_even_count(a@),
                co0 as int == initial_odd_count(a@),
                ce0 >= 0,
                co0 >= 0,
                ce0 + co0 == n as i64,
                ce0 <= 100_000,
                co0 <= 100_000,
                s0 >= 0,
                s0 <= 100_000_000_000_000i64,
                sum as int == state_after(s0 as int, ce0 as int, co0 as int, qtypes@, qxs@, k as int).0,
                ce as int == state_after(s0 as int, ce0 as int, co0 as int, qtypes@, qxs@, k as int).1,
                co as int == state_after(s0 as int, ce0 as int, co0 as int, qtypes@, qxs@, k as int).2,
                ce >= 0, co >= 0,
                ce <= 100_000, co <= 100_000,
                ce + co == ce0 + co0,
                sum >= 0,
                sum <= 100_000_000_000_000i64 + (k as i64) * 1_000_000_000,
                forall|kk: int| 0 <= kk < k as int ==> #[trigger] result[kk] as int == state_after(s0 as int, ce0 as int, co0 as int, qtypes@, qxs@, kk + 1).0,
            decreases q - k,
        {
            let t = qtypes[k];
            let x = qxs[k] as i64;
            let prev_sum = sum;
            let prev_ce = ce;
            let prev_co = co;
            assert(ce <= 100_000 && co <= 100_000 && x <= 10_000);
            assert(ce * x <= 1_000_000_000) by (nonlinear_arith)
                requires 0 <= ce <= 100_000, 0 <= x <= 10_000;
            assert(co * x <= 1_000_000_000) by (nonlinear_arith)
                requires 0 <= co <= 100_000, 0 <= x <= 10_000;
            if t == 0 {
                sum += ce * x;
                if x % 2 == 1 {
                    co += ce;
                    ce = 0;
                }
            } else {
                sum += co * x;
                if x % 2 == 1 {
                    ce += co;
                    co = 0;
                }
            }
            result.push(sum);
            proof {
                let new_state = apply_one(prev_sum as int, prev_ce as int, prev_co as int, qtypes[k as int], qxs[k as int]);
                assert(sum as int == new_state.0);
                assert(ce as int == new_state.1);
                assert(co as int == new_state.2);
            }
            k += 1;
        }
        result
    }
}

}
