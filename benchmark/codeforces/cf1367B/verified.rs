use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_odd_at_even(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        let last = a.len() - 1;
        let prev = count_odd_at_even(a.subrange(0, last));
        if last % 2 == 0 && a[last] % 2 == 1 {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn count_even_at_odd(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        let last = a.len() - 1;
        let prev = count_even_at_odd(a.subrange(0, last));
        if last % 2 == 1 && a[last] % 2 == 0 {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn count_odd_at_even_prefix(a: Seq<u32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        let prev = count_odd_at_even_prefix(a, k - 1);
        if (k - 1) % 2 == 0 && a[k - 1] % 2 == 1 {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn count_even_at_odd_prefix(a: Seq<u32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        let prev = count_even_at_odd_prefix(a, k - 1);
        if (k - 1) % 2 == 1 && a[k - 1] % 2 == 0 {
            prev + 1
        } else {
            prev
        }
    }
}

proof fn lemma_count_odd_at_even_eq_prefix(a: Seq<u32>)
    ensures
        count_odd_at_even(a) == count_odd_at_even_prefix(a, a.len() as int),
    decreases a.len(),
{
    if a.len() == 0 {
    } else {
        let last = a.len() - 1;
        lemma_count_odd_at_even_eq_prefix(a.subrange(0, last));
        lemma_count_odd_at_even_prefix_extend(a, last);
    }
}

proof fn lemma_count_odd_at_even_prefix_extend(a: Seq<u32>, k: int)
    requires
        0 <= k < a.len(),
    ensures
        count_odd_at_even_prefix(a, k) == count_odd_at_even_prefix(a.subrange(0, k), k),
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_count_odd_at_even_prefix_extend(a, k - 1);
        assert(a.subrange(0, k - 1) == a.subrange(0, k).subrange(0, k - 1));
        lemma_count_odd_at_even_prefix_extend(a.subrange(0, k), k - 1);
    }
}

proof fn lemma_count_even_at_odd_eq_prefix(a: Seq<u32>)
    ensures
        count_even_at_odd(a) == count_even_at_odd_prefix(a, a.len() as int),
    decreases a.len(),
{
    if a.len() == 0 {
    } else {
        let last = a.len() - 1;
        lemma_count_even_at_odd_eq_prefix(a.subrange(0, last));
        lemma_count_even_at_odd_prefix_extend(a, last);
    }
}

proof fn lemma_count_even_at_odd_prefix_extend(a: Seq<u32>, k: int)
    requires
        0 <= k < a.len(),
    ensures
        count_even_at_odd_prefix(a, k) == count_even_at_odd_prefix(a.subrange(0, k), k),
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_count_even_at_odd_prefix_extend(a, k - 1);
        assert(a.subrange(0, k - 1) == a.subrange(0, k).subrange(0, k - 1));
        lemma_count_even_at_odd_prefix_extend(a.subrange(0, k), k - 1);
    }
}

impl Solution {
    pub fn min_swaps(n: usize, a: Vec<u32>) -> (result: i64)
        requires
            1 <= n <= 40,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 1000u32,
        ensures
            (result == -1i64) <==> (count_odd_at_even(a@) != count_even_at_odd(a@)),
            result >= 0 ==> result == count_odd_at_even(a@),
    {
        let mut odd_at_even: i64 = 0;
        let mut even_at_odd: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                a.len() == n,
                1 <= n <= 40,
                odd_at_even == count_odd_at_even_prefix(a@, i as int),
                even_at_odd == count_even_at_odd_prefix(a@, i as int),
                0 <= odd_at_even <= i as i64,
                0 <= even_at_odd <= i as i64,
            decreases n - i,
        {
            if i % 2 == 0 && a[i] % 2 == 1 {
                odd_at_even += 1;
            } else if i % 2 == 1 && a[i] % 2 == 0 {
                even_at_odd += 1;
            }
            i += 1;
        }
        proof {
            lemma_count_odd_at_even_eq_prefix(a@);
            lemma_count_even_at_odd_eq_prefix(a@);
        }
        if odd_at_even == even_at_odd {
            odd_at_even
        } else {
            -1
        }
    }
}

}
