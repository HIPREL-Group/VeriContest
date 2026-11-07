use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_ones(seq: Seq<u8>, n: int) -> int
    recommends
        0 <= n <= seq.len(),
    decreases n,
{
    if n <= 0 {
        0int
    } else {
        let prev = count_ones(seq, n - 1);
        if seq[n - 1] == 1u8 { prev + 1 } else { prev }
    }
}

pub open spec fn min_int(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

proof fn lemma_count_ones_bounds(seq: Seq<u8>, n: int)
    requires
        0 <= n <= seq.len(),
    ensures
        0 <= count_ones(seq, n) <= n,
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_count_ones_bounds(seq, n - 1);
    }
}

impl Solution {
    pub fn min_seconds(left: Vec<u8>, right: Vec<u8>, n: usize) -> (result: usize)
        requires
            2 <= n <= 10000,
            left.len() == n,
            right.len() == n,
            forall|i: int| 0 <= i < left.len() ==> #[trigger] left[i] <= 1u8,
            forall|i: int| 0 <= i < right.len() ==> #[trigger] right[i] <= 1u8,
        ensures
            result as int == min_int(count_ones(left@, n as int), n as int - count_ones(left@, n as int))
                + min_int(count_ones(right@, n as int), n as int - count_ones(right@, n as int)),
    {
        let mut l_open: usize = 0;
        let mut r_open: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                left.len() == n,
                right.len() == n,
                2 <= n <= 10000,
                forall|j: int| 0 <= j < left.len() ==> #[trigger] left[j] <= 1u8,
                forall|j: int| 0 <= j < right.len() ==> #[trigger] right[j] <= 1u8,
                l_open as int == count_ones(left@, i as int),
                r_open as int == count_ones(right@, i as int),
                l_open <= i,
                r_open <= i,
            decreases n - i,
        {
            proof {
                lemma_count_ones_bounds(left@, i as int + 1);
                lemma_count_ones_bounds(right@, i as int + 1);
            }
            if left[i] == 1u8 {
                l_open = l_open + 1;
            }
            if right[i] == 1u8 {
                r_open = r_open + 1;
            }
            i = i + 1;
        }
        proof {
            lemma_count_ones_bounds(left@, n as int);
            lemma_count_ones_bounds(right@, n as int);
        }
        let l_min: usize = if l_open <= n - l_open { l_open } else { n - l_open };
        let r_min: usize = if r_open <= n - r_open { r_open } else { n - r_open };
        l_min + r_min
    }
}

}
