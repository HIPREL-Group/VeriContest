use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;




pub open spec fn is_valid_op(op: (int, int), n: int) -> bool {
    0 <= op.0 && op.0 <= op.1 && op.1 < n
}


pub open spec fn count_ops_covering(ops: Seq<(int, int)>, pos: int) -> int
    decreases ops.len(),
{
    if ops.len() == 0 {
        0
    } else {
        count_ops_covering(ops.drop_last(), pos)
            + if ops.last().0 <= pos && pos <= ops.last().1 { 1int } else { 0int }
    }
}


pub open spec fn apply_ops(n: int, ops: Seq<(int, int)>) -> Seq<int> {
    Seq::new(n as nat, |i: int| count_ops_covering(ops, i))
}


pub open spec fn target_as_ints(target: Seq<i32>) -> Seq<int> {
    Seq::new(target.len(), |i: int| target[i] as int)
}



pub open spec fn positive_diff_sum_int(s: Seq<int>, end: int) -> int
    decreases end,
{
    if end <= 1 {
        0
    } else {
        positive_diff_sum_int(s, end - 1)
            + if s[end - 1] > s[end - 2] { s[end - 1] - s[end - 2] } else { 0int }
    }
}

pub open spec fn algo_result_int(s: Seq<int>) -> int {
    s[0] + positive_diff_sum_int(s, s.len() as int)
}




pub open spec fn count_starting_at(ops: Seq<(int, int)>, pos: int) -> int
    decreases ops.len(),
{
    if ops.len() == 0 {
        0
    } else {
        count_starting_at(ops.drop_last(), pos)
            + if ops.last().0 == pos { 1int } else { 0int }
    }
}


pub open spec fn sum_starting_at(ops: Seq<(int, int)>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        sum_starting_at(ops, n - 1) + count_starting_at(ops, n - 1)
    }
}


pub open spec fn leftmost_positive(target: Seq<int>, from: int) -> int
    decreases target.len() - from,
{
    if from >= target.len() {
        target.len() as int
    } else if target[from] >= 1 {
        from
    } else {
        leftmost_positive(target, from + 1)
    }
}


pub open spec fn contiguous_end(target: Seq<int>, from: int) -> int
    decreases target.len() - from,
{
    if from >= target.len() - 1 || target[from + 1] < 1 {
        from
    } else {
        contiguous_end(target, from + 1)
    }
}




proof fn lemma_covering_nonneg(ops: Seq<(int, int)>, pos: int)
    ensures count_ops_covering(ops, pos) >= 0,
    decreases ops.len(),
{
    if ops.len() > 0 {
        lemma_covering_nonneg(ops.drop_last(), pos);
    }
}


proof fn lemma_starting_nonneg(ops: Seq<(int, int)>, pos: int)
    ensures count_starting_at(ops, pos) >= 0,
    decreases ops.len(),
{
    if ops.len() > 0 {
        lemma_starting_nonneg(ops.drop_last(), pos);
    }
}


proof fn lemma_starting_at_zero(ops: Seq<(int, int)>)
    requires
        forall|j: int| 0 <= j < ops.len() ==> ops[j].0 >= 0 && ops[j].0 <= ops[j].1,
    ensures
        count_starting_at(ops, 0) == count_ops_covering(ops, 0),
    decreases ops.len(),
{
    if ops.len() > 0 {
        lemma_starting_at_zero(ops.drop_last());
        let op = ops.last();
        
        
        assert(op.0 >= 0);
        assert(op.0 <= op.1);
        if op.0 == 0 {
            assert(0 <= op.1);
        }
    }
}


proof fn lemma_starting_ge_diff(ops: Seq<(int, int)>, pos: int)
    requires
        pos >= 1,
        forall|j: int| 0 <= j < ops.len() ==> ops[j].0 >= 0 && ops[j].0 <= ops[j].1,
    ensures
        count_starting_at(ops, pos) >= count_ops_covering(ops, pos) - count_ops_covering(ops, pos - 1),
        count_starting_at(ops, pos) >= 0,
    decreases ops.len(),
{
    if ops.len() == 0 {
    } else {
        let dl = ops.drop_last();
        assert forall|j: int| 0 <= j < dl.len()
            implies #[trigger] dl[j].0 >= 0 && dl[j].0 <= dl[j].1 by {
            assert(dl[j] == ops[j]);
        }
        lemma_starting_ge_diff(dl, pos);
        let a = ops.last().0;
        let b = ops.last().1;
        
        let last_j: int = ops.len() as int - 1;
        assert(ops[last_j].0 >= 0 && ops[last_j].0 <= ops[last_j].1);
        if a == pos {
            
            assert(a <= pos && pos <= b);
        } else if a < pos && pos <= b {
            
            assert(a <= pos - 1 && pos - 1 <= b);
        }
    }
}


proof fn lemma_sum_empty(n: int)
    ensures sum_starting_at(Seq::<(int, int)>::empty(), n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_sum_empty(n - 1);
    }
}


proof fn lemma_sum_drop_last(ops: Seq<(int, int)>, n: int)
    requires
        ops.len() > 0,
        ops.last().0 >= 0,
        n >= 0,
    ensures
        sum_starting_at(ops, n) ==
            sum_starting_at(ops.drop_last(), n) + if ops.last().0 < n { 1int } else { 0int },
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_sum_drop_last(ops, n - 1);
    }
}


proof fn lemma_sum_eq_len(ops: Seq<(int, int)>, n: int)
    requires
        n >= 0,
        forall|j: int| 0 <= j < ops.len() ==> 0 <= ops[j].0 && ops[j].0 < n,
    ensures
        sum_starting_at(ops, n) == ops.len() as int,
    decreases ops.len(),
{
    if ops.len() == 0 {
        assert(ops =~= Seq::<(int, int)>::empty());
        lemma_sum_empty(n);
    } else {
        let last_idx: int = ops.len() as int - 1;
        assert(0 <= last_idx < ops.len());
        let dl = ops.drop_last();
        assert forall|j: int| 0 <= j < dl.len()
            implies 0 <= #[trigger] dl[j].0 && dl[j].0 < n by {
            assert(dl[j] == ops[j]);
        }
        lemma_sum_eq_len(dl, n);
        
        assert(sum_starting_at(dl, n) == dl.len() as int);

        
        assert(0 <= ops[last_idx].0 && ops[last_idx].0 < n);
        assert(ops.last().0 >= 0);
        assert(ops.last().0 < n);
        lemma_sum_drop_last(ops, n);
        
        assert(sum_starting_at(ops, n) == sum_starting_at(dl, n) + 1);

        
        assert(dl.len() + 1 == ops.len()) by {
            assert(dl =~= ops.drop_last());
        }
        
        assert(dl.len() as int + 1 == ops.len() as int);
        assert(sum_starting_at(ops, n) == ops.len() as int);
    }
}


proof fn lemma_sum_ge_algo(target: Seq<int>, ops: Seq<(int, int)>, k: int)
    requires
        0 <= k <= target.len(),
        target.len() >= 1,
        forall|j: int| 0 <= j < ops.len() ==> is_valid_op(ops[j], target.len() as int),
        apply_ops(target.len() as int, ops) =~= target,
    ensures
        sum_starting_at(ops, k) >=
            if k <= 0 { 0int } else { target[0] + positive_diff_sum_int(target, k) },
    decreases k,
{
    let n = target.len() as int;
    
    assert forall|j: int| 0 <= j < ops.len()
        implies #[trigger] ops[j].0 >= 0 && ops[j].0 <= ops[j].1 by {
        assert(is_valid_op(ops[j], target.len() as int));
    }
    if k <= 0 {
    } else if k == 1 {
        lemma_starting_at_zero(ops);
        assert(count_ops_covering(ops, 0) == target[0]);
        
        assert(sum_starting_at(ops, 1) == sum_starting_at(ops, 0) + count_starting_at(ops, 0));
        assert(positive_diff_sum_int(target, 1) == 0int);
    } else {
        lemma_sum_ge_algo(target, ops, k - 1);
        lemma_starting_ge_diff(ops, k - 1);
        lemma_starting_nonneg(ops, k - 1);
        assert(count_ops_covering(ops, k - 1) == target[k - 1]);
        assert(count_ops_covering(ops, k - 2) == target[k - 2]);
        
        assert(sum_starting_at(ops, k) == sum_starting_at(ops, k - 1) + count_starting_at(ops, k - 1));
        if target[k - 1] > target[k - 2] {
            assert(count_starting_at(ops, k - 1) >= target[k - 1] - target[k - 2]);
        } else {
            assert(count_starting_at(ops, k - 1) >= 0);
        }
    }
}


proof fn lemma_minimality(target: Seq<int>, ops: Seq<(int, int)>, n: int)
    requires
        n >= 1,
        n == target.len(),
        forall|i: int| 0 <= i < n ==> target[i] >= 0,
        forall|j: int| 0 <= j < ops.len() ==> is_valid_op(ops[j], n),
        apply_ops(n, ops) =~= target,
    ensures
        algo_result_int(target) <= ops.len(),
{
    lemma_sum_eq_len(ops, n);
    lemma_sum_ge_algo(target, ops, n);
}




proof fn lemma_pds_nonneg(target: Seq<int>, k: int)
    requires 1 <= k <= target.len(),
    ensures positive_diff_sum_int(target, k) >= 0,
    decreases k,
{
    if k > 1 {
        lemma_pds_nonneg(target, k - 1);
    }
}


proof fn lemma_algo_nonneg(target: Seq<int>)
    requires
        target.len() >= 1,
        forall|i: int| 0 <= i < target.len() ==> target[i] >= 0,
    ensures
        algo_result_int(target) >= 0,
{
    lemma_pds_nonneg(target, target.len() as int);
}


proof fn lemma_pds_zero_monotone(target: Seq<int>, k: int)
    requires
        1 <= k <= target.len(),
        target[0] == 0,
        positive_diff_sum_int(target, k) == 0,
        forall|i: int| 0 <= i < target.len() ==> target[i] >= 0,
    ensures
        forall|i: int| 0 <= i < k ==> target[i] == 0,
    decreases k,
{
    if k <= 1 {
    } else {
        lemma_pds_nonneg(target, k - 1);
        lemma_pds_zero_monotone(target, k - 1);
    }
}


proof fn lemma_algo_zero_means_all_zero(target: Seq<int>)
    requires
        target.len() >= 1,
        forall|i: int| 0 <= i < target.len() ==> target[i] >= 0,
        algo_result_int(target) == 0,
    ensures
        forall|i: int| 0 <= i < target.len() ==> target[i] == 0,
{
    lemma_pds_nonneg(target, target.len() as int);
    assert(target[0] == 0);
    lemma_pds_zero_monotone(target, target.len() as int);
}


proof fn lemma_all_zero_pds(target: Seq<int>, k: int)
    requires
        1 <= k <= target.len(),
        forall|i: int| 0 <= i < target.len() ==> target[i] == 0,
    ensures
        positive_diff_sum_int(target, k) == 0,
    decreases k,
{
    if k > 1 {
        lemma_all_zero_pds(target, k - 1);
    }
}


proof fn lemma_leftmost_positive_props(target: Seq<int>, from: int)
    requires
        0 <= from,
        from <= target.len(),
        forall|i: int| 0 <= i < target.len() ==> target[i] >= 0,
    ensures
        from <= leftmost_positive(target, from) <= target.len(),
        leftmost_positive(target, from) < target.len()
            ==> target[leftmost_positive(target, from)] >= 1,
        forall|i: int| from <= i < leftmost_positive(target, from) ==> target[i] == 0,
    decreases target.len() - from,
{
    if from < target.len() && target[from] < 1 {
        lemma_leftmost_positive_props(target, from + 1);
    }
}


proof fn lemma_contiguous_end_props(target: Seq<int>, from: int)
    requires
        0 <= from < target.len(),
        target[from] >= 1,
    ensures
        from <= contiguous_end(target, from) < target.len(),
        forall|i: int| from <= i <= contiguous_end(target, from) ==> target[i] >= 1,
        contiguous_end(target, from) == target.len() - 1
            || target[contiguous_end(target, from) + 1] < 1,
    decreases target.len() - from,
{
    if from < target.len() - 1 && target[from + 1] >= 1 {
        lemma_contiguous_end_props(target, from + 1);
    }
}


proof fn lemma_peel_pds(target: Seq<int>, t2: Seq<int>, a: int, b: int, k: int)
    requires
        target.len() >= 1,
        t2.len() == target.len(),
        0 <= a <= b < target.len(),
        forall|i: int| 0 <= i < target.len() ==> target[i] >= 0,
        forall|i: int| a <= i <= b ==> target[i] >= 1,
        a == 0 || target[a - 1] == 0,
        b == target.len() - 1 || target[b + 1] < 1,
        t2 =~= Seq::new(target.len(), |i: int|
            target[i] - if a <= i && i <= b { 1int } else { 0int }),
        1 <= k <= target.len(),
    ensures
        positive_diff_sum_int(target, k) - positive_diff_sum_int(t2, k)
            == if a >= 1 && k > a { 1int } else { 0int },
    decreases k,
{
    if k <= 1 {
    } else {
        lemma_peel_pds(target, t2, a, b, k - 1);
        let dt = target[k - 1] - target[k - 2];
        let d2 = t2[k - 1] - t2[k - 2];
        if k - 1 == a && a >= 1 {
            
            
            
            assert(target[a - 1] == 0);
            assert(d2 == dt - 1);
            
            
            
            
        } else if k - 1 == b + 1 && b + 1 < target.len() as int {
            
            
            
            
            assert(target[b + 1] >= 0);
            assert(target[b + 1] == 0);
            assert(target[b as int] >= 1);
            assert(dt <= -1);
            assert(d2 <= 0);
        } else {
            
            
            assert(d2 == dt);
        }
    }
}


proof fn lemma_algo_peel(target: Seq<int>, a: int, b: int)
    requires
        target.len() >= 1,
        0 <= a <= b < target.len(),
        forall|i: int| 0 <= i < target.len() ==> target[i] >= 0,
        forall|i: int| a <= i <= b ==> target[i] >= 1,
        a == 0 || target[a - 1] == 0,
        b == target.len() - 1 || target[b + 1] < 1,
        algo_result_int(target) > 0,
    ensures
    {
        let t2 = Seq::new(target.len(), |i: int|
            target[i] - if a <= i && i <= b { 1int } else { 0int });
        algo_result_int(t2) == algo_result_int(target) - 1
    },
{
    let n = target.len() as int;
    let t2 = Seq::new(target.len(), |i: int|
        target[i] - if a <= i && i <= b { 1int } else { 0int });
    
    let first_diff = target[0] - t2[0];
    assert(first_diff == if a == 0 { 1int } else { 0int });
    
    lemma_peel_pds(target, t2, a, b, n);
    
    
    assert(t2.len() == target.len());
}


proof fn lemma_covering_push(ops: Seq<(int, int)>, new_op: (int, int), pos: int)
    ensures
        count_ops_covering(ops.push(new_op), pos) ==
            count_ops_covering(ops, pos)
            + if new_op.0 <= pos && pos <= new_op.1 { 1int } else { 0int },
{
    assert(ops.push(new_op).drop_last() =~= ops);
}


proof fn lemma_existence(target: Seq<int>, n: int)
    requires
        n >= 1,
        n == target.len(),
        forall|i: int| 0 <= i < n ==> target[i] >= 0,
    ensures
        exists|ops: Seq<(int, int)>|
            ops.len() as int == algo_result_int(target)
            && (forall|j: int| 0 <= j < ops.len() ==> is_valid_op(#[trigger] ops[j], n))
            && apply_ops(n, ops) =~= target,
    decreases algo_result_int(target),
{
    lemma_algo_nonneg(target);
    if algo_result_int(target) == 0 {
        
        lemma_algo_zero_means_all_zero(target);
        let witness: Seq<(int, int)> = Seq::empty();
        assert forall|i: int| 0 <= i < n implies
            count_ops_covering(witness, i) == target[i] by {}
        assert(apply_ops(n, witness) =~= target);
    } else {
        
        lemma_leftmost_positive_props(target, 0);
        let a = leftmost_positive(target, 0);
        
        if a >= n {
            
            lemma_all_zero_pds(target, n);
            assert(algo_result_int(target) == 0);
            assert(false);
        }
        let b = contiguous_end(target, a);
        lemma_contiguous_end_props(target, a);

        let t2 = Seq::new(n as nat, |i: int|
            target[i] - if a <= i && i <= b { 1int } else { 0int });

        
        assert forall|i: int| 0 <= i < n implies t2[i] >= 0 by {
            if a <= i && i <= b {
                assert(target[i] >= 1);
            }
        }

        
        if a > 0 {
            assert(target[a - 1] == 0);
        }

        
        lemma_algo_peel(target, a, b);
        let ghost algo_t2 = algo_result_int(t2);

        
        assert(t2.len() == n);
        lemma_existence(t2, n);

        let ops_prime: Seq<(int, int)> = choose|w: Seq<(int, int)>|
            w.len() as int == algo_result_int(t2)
            && (forall|j: int| 0 <= j < w.len() ==> is_valid_op(#[trigger] w[j], n))
            && apply_ops(n, w) =~= t2;

        let witness = ops_prime.push((a, b));

        
        assert(witness.len() as int == algo_result_int(target));

        
        assert forall|j: int| 0 <= j < witness.len()
            implies is_valid_op(#[trigger] witness[j], n) by {
            if j < ops_prime.len() as int {
                assert(witness[j] == ops_prime[j]);
            } else {
                assert(witness[j] == (a, b));
            }
        }

        
        assert forall|i: int| 0 <= i < n implies
            count_ops_covering(witness, i) == target[i] by {
            lemma_covering_push(ops_prime, (a, b), i);
            
            
            assert(count_ops_covering(ops_prime, i) == t2[i]);
        }
        assert(apply_ops(n, witness) =~= target);
    }
}



proof fn lemma_pds_monotone(s: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        positive_diff_sum_int(s, i) <= positive_diff_sum_int(s, j),
    decreases j - i,
{
    if i < j {
        lemma_pds_monotone(s, i, j - 1);
    }
}



impl Solution {
    pub fn min_number_operations(target: Vec<i32>) -> (result: i32)
        requires
            1 <= target.len() <= 100_000,
            forall|i: int| 0 <= i < target.len() ==> 1 <= #[trigger] target[i] <= 100_000,
            algo_result_int(target_as_ints(target@)) <= i32::MAX as int,
        ensures
            result >= 0,
            
            exists|ops: Seq<(int, int)>| {
                &&& ops.len() == result as nat
                &&& forall|j: int| 0 <= j < ops.len()
                    ==> is_valid_op(#[trigger] ops[j], target.len() as int)
                &&& apply_ops(target.len() as int, ops) =~= target_as_ints(target@)
            },
            
            forall|ops: Seq<(int, int)>|
                (forall|j: int| 0 <= j < ops.len()
                    ==> is_valid_op(#[trigger] ops[j], target.len() as int))
                && apply_ops(target.len() as int, ops) =~= target_as_ints(target@)
                ==> result as int <= ops.len(),
    {
        let ghost s = target_as_ints(target@);
        let n = target.len();
        let mut ops: i32 = target[0];

        for i in 1..n
            invariant
                n == target.len(),
                1 <= n <= 100_000,
                forall|k: int| 0 <= k < target.len() ==> 1 <= #[trigger] target[k] <= 100_000,
                algo_result_int(s) <= i32::MAX as int,
                s =~= target_as_ints(target@),
                ops as int == s[0] + positive_diff_sum_int(s, i as int),
                1 <= ops <= i32::MAX,
        {
            proof {
                lemma_pds_monotone(s, (i + 1) as int, n as int);
            }
            if target[i] > target[i - 1] {
                ops = ops + (target[i] - target[i - 1]);
            }
        }

        assert(ops as int == algo_result_int(s));

        proof {
            
            lemma_existence(s, n as int);
            let witness: Seq<(int, int)> = choose|w: Seq<(int, int)>|
                w.len() as int == algo_result_int(s)
                && (forall|j: int| 0 <= j < w.len()
                    ==> is_valid_op(#[trigger] w[j], n as int))
                && apply_ops(n as int, w) =~= s;

            
            assert forall|any_ops: Seq<(int, int)>|
                (forall|j: int| 0 <= j < any_ops.len()
                    ==> is_valid_op(#[trigger] any_ops[j], target.len() as int))
                && apply_ops(target.len() as int, any_ops) =~= target_as_ints(target@)
                implies ops as int <= #[trigger] any_ops.len() by {
                lemma_minimality(s, any_ops, n as int);
            }
        }

        ops
    }
}

} 
