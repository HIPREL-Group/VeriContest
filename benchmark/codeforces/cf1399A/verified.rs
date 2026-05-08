use vstd::prelude::*;
use vstd::seq::group_seq_axioms;
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

pub open spec fn sorted_adjacent_steps_at_most_one(s: Seq<i32>, n: int) -> bool {
    n <= s.len()
        && forall|i: int|
            0 <= i < n - 1 ==> {
                &&& #[trigger] s[i] <= s[i + 1]
                &&& (s[i + 1] as int - s[i] as int) <= 1
            }
}

pub open spec fn spec_remove_smallest_possible(a: Seq<i32>) -> bool {
    a.len() >= 1 && exists|s: Seq<i32>|
        s.len() == a.len() && same_multiset(s, a)
            && sorted_adjacent_steps_at_most_one(s, a.len() as int)
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

proof fn lemma_same_multiset_drop_first(s1: Seq<i32>, s2: Seq<i32>)
    requires
        s1.len() >= 1,
        s2.len() >= 1,
        s1.len() == s2.len(),
        same_multiset(s1, s2),
        s1[0] == s2[0],
    ensures
        same_multiset(s1.drop_first(), s2.drop_first()),
{
    broadcast use group_seq_axioms;
    broadcast use group_to_multiset_ensures;
    assert(s1.remove(0) =~= s1.drop_first());
    assert(s2.remove(0) =~= s2.drop_first());
    assert(s1.to_multiset() =~= s2.to_multiset());
    assert(s1.remove(0).to_multiset() =~= s1.to_multiset().remove(s1[0]));
    assert(s2.remove(0).to_multiset() =~= s2.to_multiset().remove(s2[0]));
    assert(s1.to_multiset().remove(s1[0]) =~= s2.to_multiset().remove(s2[0]));
    assert(s1.drop_first().to_multiset() =~= s2.drop_first().to_multiset());
}

proof fn lemma_sorted_first_le_index(s: Seq<i32>, n: int, j: int)
    requires
        0 <= j < n,
        sorted_non_decreasing(s, n),
    ensures
        s[0] <= s[j],
    decreases j,
{
    if j == 0 {
    } else {
        lemma_sorted_first_le_index(s, n, (j - 1) as int);
        assert(0 <= (j - 1) < n - 1);
        assert(s[(j - 1) as int] <= s[j]);
    }
}

proof fn lemma_sorted_nd_drop_suffix(s: Seq<i32>, n: int)
    requires
        n >= 2,
        s.len() == n,
        sorted_non_decreasing(s, n),
    ensures
        sorted_non_decreasing(s.drop_first(), n - 1),
{
    broadcast use group_seq_axioms;
    assert(s.drop_first() =~= s.subrange(1, n as int));
    assert forall|i: int|
        0 <= i < n - 2 implies #[trigger] s.drop_first()[i] <= s.drop_first()[i + 1]
    by {
        assert(0 <= i < n - 2);
        assert(0 <= i < n - 1);
        assert(s.drop_first()[i] == s[i + 1]);
        assert(0 <= i + 1 < n - 1);
        assert(s.drop_first()[i + 1] == s[i + 2]);
        assert(0 <= i + 1 < n - 1);
        assert(s[i + 1] <= s[i + 2]);
    };
}

proof fn lemma_same_multiset_sorted_nd_eq(s1: Seq<i32>, s2: Seq<i32>, n: int)
    requires
        n == s1.len() == s2.len(),
        same_multiset(s1, s2),
        sorted_non_decreasing(s1, n),
        sorted_non_decreasing(s2, n),
    ensures
        s1 =~= s2,
    decreases n,
{
    if n == 0 {
    } else {
        assert(s1[0] == s2[0]) by {
            broadcast use group_to_multiset_ensures;
            if s1[0] < s2[0] {
                assert forall|j: int| 0 <= j < n implies s1[0] < s2[j] by {
                    lemma_sorted_first_le_index(s2, n, j);
                    assert(s2[0] <= s2[j]);
                };
                assert(s2.to_multiset().count(s1[0]) == 0);
                assert(s1.to_multiset().count(s1[0]) >= 1);
                assert(s1.to_multiset() =~= s2.to_multiset());
                assert(false);
            } else if s2[0] < s1[0] {
                assert forall|j: int| 0 <= j < n implies s2[0] < s1[j] by {
                    lemma_sorted_first_le_index(s1, n, j);
                };
                assert(s1.to_multiset().count(s2[0]) == 0);
                assert(s2.to_multiset().count(s2[0]) >= 1);
                assert(false);
            } else {
            }
        };
        assert(n >= 1);
        lemma_same_multiset_drop_first(s1, s2);
        if n >= 2 {
            lemma_sorted_nd_drop_suffix(s1, n);
            lemma_sorted_nd_drop_suffix(s2, n);
        }
        assert(sorted_non_decreasing(s1.drop_first(), n - 1));
        assert(sorted_non_decreasing(s2.drop_first(), n - 1));
        lemma_same_multiset_sorted_nd_eq(s1.drop_first(), s2.drop_first(), n - 1);
        assert(s1.drop_first() =~= s2.drop_first());
        assert_seqs_equal!(s1, s2, kk => {
            if kk == 0 {
                assert(s1[0] == s2[0]);
            } else {
                assert(s1[kk] == s1.drop_first()[(kk - 1)]);
                assert(s2[kk] == s2.drop_first()[(kk - 1)]);
                assert(s1.drop_first()[(kk - 1)] == s2.drop_first()[(kk - 1)]);
            }
        });
        assert(s1 =~= s2);
    }
}

proof fn lemma_spec_len_one(a: Seq<i32>)
    requires
        a.len() == 1,
    ensures
        spec_remove_smallest_possible(a),
{
    assert(same_multiset(a, a));
    assert(sorted_adjacent_steps_at_most_one(a, 1));
    assert(spec_remove_smallest_possible(a));
}

proof fn lemma_spec_from_sorted_arr(orig: Seq<i32>, arr: Seq<i32>, n: int)
    requires
        n == orig.len() == arr.len(),
        n >= 1,
        same_multiset(arr, orig),
        sorted_adjacent_steps_at_most_one(arr, n),
    ensures
        spec_remove_smallest_possible(orig),
{
    assert(same_multiset(arr, orig));
    assert(sorted_adjacent_steps_at_most_one(arr, n));
    assert(spec_remove_smallest_possible(orig));
}

proof fn lemma_spec_implies_adjacent(orig: Seq<i32>, arr: Seq<i32>, n: int)
    requires
        n >= 2,
        n == orig.len() == arr.len(),
        same_multiset(arr, orig),
        sorted_non_decreasing(arr, n),
        spec_remove_smallest_possible(orig),
    ensures
        sorted_adjacent_steps_at_most_one(arr, n),
{
    assert(exists|w: Seq<i32>|
        w.len() == n && same_multiset(w, orig) && sorted_adjacent_steps_at_most_one(w, n));
    assert forall|w: Seq<i32>|
        w.len() == n && same_multiset(w, orig) && sorted_adjacent_steps_at_most_one(w, n)
            implies sorted_adjacent_steps_at_most_one(arr, n)
    by {
        assert(sorted_non_decreasing(w, n));
        lemma_same_multiset_sorted_nd_eq(w, arr, n);
        assert_seqs_equal!(w, arr, idx => { });
        assert(sorted_adjacent_steps_at_most_one(w, n));
    };
    assert(sorted_adjacent_steps_at_most_one(arr, n));
}

proof fn lemma_not_spec_bad_gap(orig: Seq<i32>, arr: Seq<i32>, n: int, bad: int)
    requires
        n >= 2,
        n == orig.len() == arr.len(),
        same_multiset(arr, orig),
        sorted_non_decreasing(arr, n),
        0 <= bad < n - 1,
        (arr[bad + 1] as int) > (arr[bad] as int) + 1,
    ensures
        !spec_remove_smallest_possible(orig),
{
    assert(!sorted_adjacent_steps_at_most_one(arr, n)) by {
        assert(!((arr[bad + 1] as int - arr[bad] as int) <= 1));
    };
    if spec_remove_smallest_possible(orig) {
        lemma_spec_implies_adjacent(orig, arr, n);
        assert(false);
    } else {
    }
}

impl Solution {
    pub fn remove_smallest_possible(a: Vec<i32>) -> (res: bool)
        requires
            1 <= a.len() <= 50,
            forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] as int <= 100,
        ensures
            res == spec_remove_smallest_possible(a@),
    {
        let n = a.len();
        if n == 1 {
            proof {
                lemma_spec_len_one(a@);
            }
            return true;
        }
        let ghost orig = a@;
        let mut arr = Vec::new();
        let mut i = 0usize;
        while i < n
            invariant
                n == a.len(),
                arr.len() == i,
                i <= n,
                a@ == orig,
                forall|k: int| 0 <= k < i ==> arr@[k] == a@[k],
            decreases
                n - i,
        {
            arr.push(a[i]);
            i += 1;
        }
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
                a@ == orig,
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
        proof {
            assert(sorted_non_decreasing(arr@, n as int));
        }
        let mut k = 0usize;
        while k + 1 < n
            invariant
                arr.len() == n,
                (k as int) < (n as int),
                a@ == orig,
                same_multiset(arr@, orig),
                sorted_non_decreasing(arr@, n as int),
                forall|t: int|
                    0 <= t < k as int ==> #[trigger] arr@[t] <= arr@[t + 1]
                        && (arr@[t + 1] as int - arr@[t] as int) <= 1,
            decreases
                n - 1 - k,
        {
            proof {
                assert((k as int) + 1 < (n as int));
                assert(0 <= (k as int) < (n as int) - 1);
                assert((k + 1) < n);
                assert(arr@[k as int] <= arr@[k as int + 1]);
            }
            if (arr[k + 1] as i64) > (arr[k] as i64) + 1 {
                proof {
                    assert((arr@[k as int + 1] as int) > (arr@[k as int] as int) + 1);
                    lemma_not_spec_bad_gap(orig, arr@, n as int, k as int);
                    assert(!spec_remove_smallest_possible(orig));
                    assert(a@ == orig);
                    assert(!spec_remove_smallest_possible(a@));
                }
                return false;
            }
            k += 1;
        }
        proof {
            assert(forall|t: int|
                0 <= t < n as int - 1 ==> #[trigger] arr@[t] <= arr@[t + 1]
                    && (arr@[t + 1] as int - arr@[t] as int) <= 1);
            assert(sorted_adjacent_steps_at_most_one(arr@, n as int));
            lemma_spec_from_sorted_arr(orig, arr@, n as int);
        }
        true
    }
}

}
