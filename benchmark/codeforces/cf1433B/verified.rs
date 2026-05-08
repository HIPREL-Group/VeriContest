use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn first_one_idx(a: Seq<u8>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        -1
    } else {
        let r = first_one_idx(a, k - 1);
        if r != -1 {
            r
        } else if a[k - 1] == 1u8 {
            k - 1
        } else {
            -1
        }
    }
}

pub open spec fn last_one_idx(a: Seq<u8>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        -1
    } else if a[k - 1] == 1u8 {
        k - 1
    } else {
        last_one_idx(a, k - 1)
    }
}

pub open spec fn count_zeros_prefix(a: Seq<u8>, lo: int, k: int) -> int
    decreases k - lo,
{
    if k <= lo {
        0
    } else {
        let prev = count_zeros_prefix(a, lo, k - 1);
        if a[k - 1] == 0u8 { prev + 1 } else { prev }
    }
}

proof fn lemma_exists_implies_first_one(a: Seq<u8>, n: int)
    requires
        0 <= n <= a.len(),
        exists|i: int| 0 <= i < n && #[trigger] a[i] == 1u8,
    ensures
        first_one_idx(a, n) != -1,
        0 <= first_one_idx(a, n) < n,
    decreases n,
{
    if n == 0 {
        assert(false);
    } else {
        let r = first_one_idx(a, n - 1);
        if r != -1 {
            lemma_first_one_idx_in_bounds(a, n - 1);
        } else if a[n - 1] == 1u8 {
        } else {
            
            assert(exists|i: int| 0 <= i < n && #[trigger] a[i] == 1u8);
            let w = choose|i: int| 0 <= i < n && #[trigger] a[i] == 1u8;
            assert(w < n - 1 || w == n - 1);
            if w == n - 1 {
                assert(a[n - 1] == 1u8);
                assert(false);
            } else {
                assert(0 <= w < n - 1);
                assert(exists|i: int| 0 <= i < n - 1 && #[trigger] a[i] == 1u8);
                lemma_exists_implies_first_one(a, n - 1);
                assert(first_one_idx(a, n - 1) != -1);
                assert(false);
            }
        }
    }
}

proof fn lemma_first_one_idx_in_bounds(a: Seq<u8>, n: int)
    requires
        0 <= n <= a.len(),
    ensures
        first_one_idx(a, n) == -1 || (0 <= first_one_idx(a, n) < n),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_first_one_idx_in_bounds(a, n - 1);
    }
}

proof fn lemma_exists_implies_last_one(a: Seq<u8>, n: int)
    requires
        0 <= n <= a.len(),
        exists|i: int| 0 <= i < n && #[trigger] a[i] == 1u8,
    ensures
        last_one_idx(a, n) != -1,
        0 <= last_one_idx(a, n) < n,
    decreases n,
{
    if n == 0 {
        assert(false);
    } else if a[n - 1] == 1u8 {
    } else {
        let w = choose|i: int| 0 <= i < n && #[trigger] a[i] == 1u8;
        if w == n - 1 {
            assert(false);
        } else {
            assert(0 <= w < n - 1);
            assert(exists|i: int| 0 <= i < n - 1 && #[trigger] a[i] == 1u8);
            lemma_exists_implies_last_one(a, n - 1);
            lemma_last_one_idx_in_bounds(a, n - 1);
        }
    }
}

proof fn lemma_last_one_idx_in_bounds(a: Seq<u8>, n: int)
    requires
        0 <= n <= a.len(),
    ensures
        last_one_idx(a, n) == -1 || (0 <= last_one_idx(a, n) < n),
    decreases n,
{
    if n == 0 {
    } else if a[n - 1] == 1u8 {
    } else {
        lemma_last_one_idx_in_bounds(a, n - 1);
    }
}

proof fn lemma_last_one_idx_lower_bound(a: Seq<u8>, n: int)
    requires
        0 <= n <= a.len(),
    ensures
        last_one_idx(a, n) == -1 || (0 <= last_one_idx(a, n) < n),
        
        n + 1 <= a.len() ==> last_one_idx(a, n + 1) >= last_one_idx(a, n) || last_one_idx(a, n + 1) == n,
    decreases n,
{
    lemma_last_one_idx_in_bounds(a, n);
}

proof fn lemma_first_one_idx_le_last(a: Seq<u8>, n: int)
    requires
        0 <= n <= a.len(),
        first_one_idx(a, n) != -1,
    ensures
        last_one_idx(a, n) != -1,
        first_one_idx(a, n) <= last_one_idx(a, n),
    decreases n,
{
    if n == 0 {
        assert(false);
    } else {
        let r = first_one_idx(a, n - 1);
        if r != -1 {
            lemma_first_one_idx_le_last(a, n - 1);
            lemma_last_one_idx_in_bounds(a, n - 1);
            if a[n - 1] == 1u8 {
                
                lemma_first_one_idx_in_bounds(a, n - 1);
                assert(r < n - 1);
                assert(last_one_idx(a, n) == n - 1);
                assert(first_one_idx(a, n) == r);
            } else {
                assert(last_one_idx(a, n) == last_one_idx(a, n - 1));
                assert(first_one_idx(a, n) == r);
            }
        } else if a[n - 1] == 1u8 {
            assert(first_one_idx(a, n) == n - 1);
            assert(last_one_idx(a, n) == n - 1);
        } else {
            assert(first_one_idx(a, n) == -1);
            assert(false);
        }
    }
}

impl Solution {
    pub fn min_moves_books(n: usize, a: Vec<u8>) -> (result: usize)
        requires
            1 <= n <= 50,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 1u8,
            exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == 1u8,
        ensures
            result as int == count_zeros_prefix(a@, first_one_idx(a@, n as int), last_one_idx(a@, n as int) + 1),
    {
        let mut first: usize = 0;
        let mut found_first = false;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                a.len() == n,
                1 <= n <= 50,
                forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] <= 1u8,
                found_first <==> first_one_idx(a@, i as int) != -1,
                found_first ==> (first as int) == first_one_idx(a@, i as int),
                found_first ==> first < i,
            decreases n - i,
        {
            if a[i] == 1u8 && !found_first {
                first = i;
                found_first = true;
            }
            i += 1;
        }
        let mut last: usize = 0;
        let mut found_last = false;
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                a.len() == n,
                1 <= n <= 50,
                forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] <= 1u8,
                found_last <==> last_one_idx(a@, j as int) != -1,
                found_last ==> (last as int) == last_one_idx(a@, j as int),
                found_last ==> last < j,
                found_first <==> first_one_idx(a@, n as int) != -1,
                found_first ==> (first as int) == first_one_idx(a@, n as int),
            decreases n - j,
        {
            if a[j] == 1u8 {
                last = j;
                found_last = true;
            }
            j += 1;
        }
        proof {
            lemma_exists_implies_first_one(a@, n as int);
            lemma_exists_implies_last_one(a@, n as int);
            lemma_first_one_idx_le_last(a@, n as int);
        }
        if !found_first || !found_last {
            assert(false);
            return 0;
        }
        let mut count: usize = 0;
        let mut k: usize = first;
        while k <= last
            invariant
                first <= k <= last + 1,
                last < n,
                first <= last,
                a.len() == n,
                1 <= n <= 50,
                forall|m: int| 0 <= m < a.len() ==> #[trigger] a[m] <= 1u8,
                count as int == count_zeros_prefix(a@, first as int, k as int),
                count as int <= k as int - first as int,
                first as int == first_one_idx(a@, n as int),
                last as int == last_one_idx(a@, n as int),
            decreases last + 1 - k,
        {
            if a[k] == 0u8 {
                count += 1;
            }
            k += 1;
        }
        count
    }
}

}
