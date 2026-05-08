use vstd::prelude::*;
use vstd::seq_lib::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sorted_non_decreasing(seq: Seq<i32>, n: int) -> bool {
    n <= seq.len()
        && forall|i: int| 0 <= i < n - 1 ==> #[trigger] seq[i] <= seq[i + 1]
}

pub open spec fn same_multiset(left: Seq<i32>, right: Seq<i32>) -> bool {
    left.len() == right.len() && left.to_multiset() =~= right.to_multiset()
}

proof fn lemma_seq_eq_same_multiset(s1: Seq<i32>, s2: Seq<i32>)
    requires
        s1 =~= s2,
    ensures
        same_multiset(s1, s2),
    decreases s1.len(),
{
    broadcast use group_to_multiset_ensures;
    if s1.len() == 0 {
        assert(s2.len() == 0);
        assert(s1.to_multiset() =~= s2.to_multiset());
    } else {
        assert(s1.len() == s2.len());
        assert(s1.first() == s2.first());
        assert(s1.drop_first() =~= s2.drop_first());
        lemma_seq_eq_same_multiset(s1.drop_first(), s2.drop_first());
        to_multiset_build(s1.drop_first(), s1.first());
        to_multiset_build(s2.drop_first(), s2.first());
        assert(s1.to_multiset() =~= s2.to_multiset());
    }
}

proof fn lemma_multiset_swap(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i < seq.len(),
        0 <= j < seq.len(),
        i != j,
    ensures
        seq.update(i, seq[j]).update(j, seq[i]).to_multiset() =~= seq.to_multiset(),
{
    broadcast use group_to_multiset_ensures;
    let after_first = seq.update(i, seq[j]);
    assert(after_first.to_multiset() =~= seq.to_multiset().insert(seq[j]).remove(seq[i]));
    assert(after_first[j] == seq[j]);
    assert(after_first.update(j, seq[i]).to_multiset()
        =~= after_first.to_multiset().insert(seq[i]).remove(after_first[j]));
}

impl Solution {
    pub fn gravity_flip(a: Vec<i32>, n: usize) -> (result: Vec<i32>)
        requires
            1 <= n <= 100,
            a.len() == n,
            forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] a[i] as int <= 100,
        ensures
            result.len() == n,
            sorted_non_decreasing(result@, n as int),
            same_multiset(result@, a@),
    {
        let mut arr = Vec::new();
        let mut i = 0usize;
        while i < n
            invariant
                n == a.len(),
                arr.len() == i,
                i <= n,
                forall|k: int| 0 <= k < i ==> arr@[k] == a@[k],
            decreases
                n - i,
        {
            arr.push(a[i]);
            i += 1;
        }
        let ghost orig = a@;
        proof {
            assert(arr@.len() == orig.len());
            assert(forall|k: int| 0 <= k < arr@.len() ==> arr@[k] == orig[k]);
            assert(arr@ =~= orig);
            lemma_seq_eq_same_multiset(arr@, orig);
        }
        i = 0usize;
        while i < n
            invariant
                arr.len() == n,
                same_multiset(arr@, orig),
                forall|p: int, q: int| 0 <= p < q < i as int ==> arr@[p] <= arr@[q],
                forall|p: int, r: int| 0 <= p < i as int && i as int <= r < n as int
                    ==> arr@[p] <= arr@[r],
            decreases
                n - i,
        {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n
                invariant
                    arr.len() == n,
                    i <= min_idx,
                    min_idx < n,
                    i < j <= n,
                    forall|k: int| i as int <= k < j as int && 0 <= k < n as int
                        ==> arr@[min_idx as int] <= arr@[k],
                decreases
                    n - j,
            {
                if arr[j] < arr[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            if i != min_idx {
                proof {
                    lemma_multiset_swap(arr@, i as int, min_idx as int);
                }
                let tmp = arr[i];
                arr.set(i, arr[min_idx]);
                arr.set(min_idx, tmp);
            }
            i += 1;
        }
        arr
    }
}

}
