use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_seq(seq: Seq<i32>, n: int) -> int
    recommends 1 <= n <= seq.len(),
    decreases n,
{
    if n <= 1 {
        seq[0] as int
    } else {
        let prev = min_seq(seq, n - 1);
        if (seq[n - 1] as int) < prev { seq[n - 1] as int } else { prev }
    }
}

pub open spec fn has_value_strictly_greater(seq: Seq<i32>, n: int, m: int) -> bool {
    exists|i: int| 0 <= i < n && (#[trigger] seq[i]) as int > m
}

pub open spec fn is_smallest_above(seq: Seq<i32>, n: int, m: int, v: int) -> bool {
    (exists|i: int| 0 <= i < n && (#[trigger] seq[i]) as int == v && v > m)
    && (forall|j: int| 0 <= j < n ==> (#[trigger] seq[j]) as int <= m || (seq[j]) as int >= v)
}

proof fn lemma_min_seq_le_all(seq: Seq<i32>, n: int)
    requires 1 <= n <= seq.len(),
    ensures forall|i: int| 0 <= i < n ==> min_seq(seq, n) <= (#[trigger] seq[i]) as int,
    decreases n,
{
    if n == 1 {
    } else {
        lemma_min_seq_le_all(seq, n - 1);
    }
}

proof fn lemma_min_seq_attained(seq: Seq<i32>, n: int)
    requires 1 <= n <= seq.len(),
    ensures exists|i: int| 0 <= i < n && (#[trigger] seq[i]) as int == min_seq(seq, n),
    decreases n,
{
    if n == 1 {
        assert(seq[0] as int == min_seq(seq, n));
    } else {
        lemma_min_seq_attained(seq, n - 1);
        if (seq[n - 1] as int) < min_seq(seq, n - 1) {
            assert(seq[n - 1] as int == min_seq(seq, n));
        } else {
            let i = choose|i: int| 0 <= i < n - 1 && (seq[i]) as int == min_seq(seq, n - 1);
            assert((seq[i]) as int == min_seq(seq, n));
        }
    }
}

impl Solution {
    pub fn second_min(a: Vec<i32>, n: usize) -> (result: Option<i32>)
        requires
            1 <= n <= 100,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> -100 <= #[trigger] a[i] as int <= 100,
        ensures
            ({
                let m = min_seq(a@, n as int);
                result.is_some() <==> has_value_strictly_greater(a@, n as int, m)
            }),
            result.is_some() ==> is_smallest_above(a@, n as int, min_seq(a@, n as int), result.unwrap() as int),
    {
        let mut min_val: i32 = a[0];
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == a.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < a.len() ==> -100 <= #[trigger] a[j] as int <= 100,
                min_val as int == min_seq(a@, i as int),
            decreases n - i,
        {
            if a[i] < min_val {
                min_val = a[i];
            }
            i = i + 1;
        }
        
        let mut found: bool = false;
        let mut second: i32 = 0i32;
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == a.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < a.len() ==> -100 <= #[trigger] a[j] as int <= 100,
                min_val as int == min_seq(a@, n as int),
                found ==> (exists|p: int| 0 <= p < k && (#[trigger] a[p]) as int == second as int && (second as int) > (min_val as int)),
                found ==> (forall|p: int| 0 <= p < k ==> (#[trigger] a[p]) as int <= (min_val as int) || (a[p]) as int >= (second as int)),
                !found ==> (forall|p: int| 0 <= p < k ==> (#[trigger] a[p]) as int <= (min_val as int)),
            decreases n - k,
        {
            if a[k] > min_val {
                if !found || a[k] < second {
                    second = a[k];
                    found = true;
                }
            }
            k = k + 1;
        }
        if found {
            Some(second)
        } else {
            None
        }
    }
}

}
